use super::Result;

#[derive(Clone, Debug)]
pub struct Token {
    pub start: usize,
    pub end: usize,
    pub text: String,
    pub directive: Option<usize>,
}

#[derive(Debug)]
pub struct Directive {
    pub end: usize,
    pub tokens: std::ops::Range<usize>,
}

pub struct Lexed {
    pub tokens: Vec<Token>,
    pub directives: Vec<Directive>,
}

fn splice(bytes: &[u8], i: usize) -> Option<usize> {
    if bytes.get(i) != Some(&b'\\') {
        return None;
    }
    match bytes.get(i + 1..) {
        Some([b'\n', ..]) => Some(i + 2),
        Some([b'\r', b'\n', ..]) => Some(i + 3),
        _ => None,
    }
}

fn directive_end(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() {
        if let Some(end) = splice(bytes, i) {
            i = end;
        } else if bytes[i] == b'\n' {
            return i;
        } else {
            i += 1;
        }
    }
    i
}

fn ident(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte >= 128
}

fn character_end(source: &str, start: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut end = start + 1;
    if bytes.get(end) == Some(&b'\\') {
        end += 1;
        if bytes.get(end) == Some(&b'\'') {
            end += 1;
        } else {
            while bytes.get(end).is_some_and(|byte| {
                !matches!(byte, b'\'' | b'\n' | b'\r') && !byte.is_ascii_whitespace()
            }) {
                end += 1;
            }
        }
    } else {
        end += source.get(end..)?.chars().next()?.len_utf8();
    }
    if bytes.get(end) == Some(&b'\'') {
        return Some(end + 1);
    }
    // C also permits multicharacter literals. Do not mistake Pulse's
    // apostrophe-prefixed identifiers for those literals.
    while bytes.get(end).is_some_and(u8::is_ascii_alphanumeric) {
        end += 1;
    }
    (bytes.get(end) == Some(&b'\'')).then_some(end + 1)
}

pub fn lex(source: &str) -> Result<Lexed> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut directives: Vec<Directive> = Vec::new();
    let mut active = None;
    let mut line_start = true;
    let mut i = 0;
    while i < bytes.len() {
        if active.is_some_and(|n: usize| i >= directives[n].end) {
            active = None;
        }
        if let Some(end) = splice(bytes, i) {
            i = end;
            continue;
        }
        if bytes[i].is_ascii_whitespace() {
            if bytes[i] == b'\n' {
                line_start = true;
            }
            i += 1;
            continue;
        }
        if bytes[i..].starts_with(b"//") {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i = splice(bytes, i).unwrap_or(i + 1);
            }
            continue;
        }
        if bytes[i..].starts_with(b"/*") {
            let Some(length) = source[i + 2..].find("*/") else {
                return Err(format!("unterminated comment at byte {i}"));
            };
            let end = i + 2 + length + 2;
            if source[i..end].contains('\n') {
                line_start = true;
            }
            i = end;
            continue;
        }
        if bytes[i] == b'#' && line_start && active.is_none() {
            active = Some(directives.len());
            directives.push(Directive {
                end: directive_end(bytes, i),
                tokens: tokens.len()..tokens.len(),
            });
        }
        line_start = false;
        let start = i;
        if bytes[i] == b'"' {
            i += 1;
            loop {
                match bytes.get(i) {
                    Some(b'\\') => {
                        i = splice(bytes, i).unwrap_or(i + 2);
                    }
                    Some(b'"') => {
                        i += 1;
                        break;
                    }
                    None | Some(b'\n' | b'\r') => {
                        return Err(format!("unterminated string at byte {start}"));
                    }
                    _ => i += 1,
                }
            }
        } else if bytes[i] == b'\'' {
            i = character_end(source, i).unwrap_or(i + 1);
        } else if ident(bytes[i]) {
            i += 1;
            while i < bytes.len() && ident(bytes[i]) {
                i += 1;
            }
        } else {
            let operators = [
                "...", "<<=", ">>=", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&",
                "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "##",
            ];
            i += operators
                .iter()
                .find(|operator| source[start..].starts_with(**operator))
                .map_or(1, |operator| operator.len());
        }
        tokens.push(Token {
            start,
            end: i,
            text: source[start..i].replace("\\\r\n", "").replace("\\\n", ""),
            directive: active,
        });
        if let Some(n) = active {
            directives[n].tokens.end = tokens.len();
        }
    }
    Ok(Lexed { tokens, directives })
}

pub fn texts(tokens: &[Token]) -> Vec<String> {
    tokens.iter().map(|token| token.text.clone()).collect()
}

pub fn close_paren(tokens: &[Token], open: usize) -> Result<usize> {
    if tokens.get(open).map(|token| token.text.as_str()) != Some("(") {
        return Err("expected '(' after annotation macro".into());
    }
    let mut depth = 0;
    for (i, token) in tokens.iter().enumerate().skip(open) {
        match token.text.as_str() {
            "(" => depth += 1,
            ")" => {
                depth -= 1;
                if depth == 0 {
                    return Ok(i);
                }
            }
            _ => {}
        }
    }
    Err(format!(
        "unclosed annotation argument at byte {}",
        tokens[open].start
    ))
}
