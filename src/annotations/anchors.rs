use super::{
    Owner, Result, Site,
    lex::{Token, lex, texts},
};
use tree_sitter::Node;

pub struct Scope {
    pub owner: Owner,
    pub start: usize,
    pub end: usize,
}

fn name(node: Node<'_>, source: &str) -> Option<String> {
    if matches!(
        node.kind(),
        "identifier" | "type_identifier" | "field_identifier"
    ) {
        return Some(source[node.byte_range()].into());
    }
    node.child_by_field_name("declarator")
        .or_else(|| node.child_by_field_name("name"))
        .and_then(|child| name(child, source))
}

fn collect(
    node: Node<'_>,
    source: &str,
    tokens: &[Token],
    context: &[String],
    scopes: &mut Vec<Scope>,
) -> Result<()> {
    let mut context = context.to_vec();
    if node.kind().starts_with("preproc_")
        && !matches!(node.kind(), "preproc_def" | "preproc_function_def")
    {
        let condition = node
            .child_by_field_name("condition")
            .or_else(|| node.child_by_field_name("name"))
            .map(|child| {
                lex(&source[child.byte_range()]).map(|lexed| texts(&lexed.tokens).join(" "))
            })
            .transpose()?
            .unwrap_or_default();
        context.push(format!("{} {condition}", node.kind()));
    }
    if matches!(
        node.kind(),
        "function_definition"
            | "declaration"
            | "type_definition"
            | "struct_specifier"
            | "union_specifier"
            | "enum_specifier"
            | "preproc_def"
            | "preproc_function_def"
    ) && let Some(name) = name(node, source)
    {
        scopes.push(Scope {
            owner: Owner {
                kind: node.kind().into(),
                name,
                context,
            },
            start: tokens.partition_point(|token| token.end <= node.start_byte()),
            end: tokens.partition_point(|token| token.start < node.end_byte()),
        });
        return Ok(());
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect(child, source, tokens, &context, scopes)?;
    }
    Ok(())
}

fn parse(source: &str) -> Result<tree_sitter::Tree> {
    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(&tree_sitter_c::LANGUAGE.into())
        .map_err(|error| error.to_string())?;
    parser
        .parse(source, None)
        .ok_or("C syntax parser did not return a tree".into())
}

pub fn standalone_statements(source: &str) -> Result<std::collections::BTreeMap<usize, usize>> {
    fn visit(node: Node<'_>, statements: &mut std::collections::BTreeMap<usize, usize>) {
        // Recovery around macros or preprocessor branches can misidentify
        // controlled statements as free-standing. Keep their no-op bodies.
        if node.kind() == "compound_statement" && node.has_error() {
            return;
        }
        if node.kind() == "expression_statement"
            && !node.has_error()
            && node
                .parent()
                .is_some_and(|parent| parent.kind() == "compound_statement")
        {
            statements.insert(node.start_byte(), node.end_byte());
        }
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            visit(child, statements);
        }
    }
    let tree = parse(source)?;
    let mut statements = std::collections::BTreeMap::new();
    visit(tree.root_node(), &mut statements);
    Ok(statements)
}

pub fn function_bodies(source: &str) -> Result<Vec<std::ops::Range<usize>>> {
    fn visit(node: Node<'_>, bodies: &mut Vec<std::ops::Range<usize>>) {
        if node.kind() == "function_definition"
            && let Some(body) = node.child_by_field_name("body")
        {
            bodies.push(body.byte_range());
            return;
        }
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            visit(child, bodies);
        }
    }
    let tree = parse(source)?;
    let mut bodies = Vec::new();
    visit(tree.root_node(), &mut bodies);
    // Opaque declaration/handler macros can make tree-sitter recover before
    // the end of a function. Also recognize balanced file-scope function
    // bodies, excluding records, directives and global initializers.
    let tokens = lex(source)?.tokens;
    let mut braces = Vec::new();
    let mut parens = 0usize;
    let mut initializer = false;
    let mut previous = "";
    for token in tokens.iter().filter(|token| token.directive.is_none()) {
        match token.text.as_str() {
            "(" => parens += 1,
            ")" => parens = parens.saturating_sub(1),
            "=" if braces.is_empty() && parens == 0 => initializer = true,
            ";" if braces.is_empty() && parens == 0 => initializer = false,
            "{" => braces.push((
                token.start,
                braces.is_empty() && parens == 0 && previous == ")" && !initializer,
            )),
            "}" => {
                if let Some((start, function)) = braces.pop()
                    && function
                {
                    bodies.push(start..token.end);
                }
                if braces.is_empty() {
                    initializer = false;
                }
            }
            _ => {}
        }
        previous = &token.text;
    }
    Ok(bodies)
}

pub fn declared_names(source: &str) -> Result<Vec<String>> {
    fn visit(node: Node<'_>, source: &str, names: &mut Vec<String>) {
        // Recovery can misread postfix annotation macros as C bindings.
        if !node.has_error()
            && matches!(
                node.kind(),
                "function_definition"
                    | "declaration"
                    | "type_definition"
                    | "parameter_declaration"
                    | "field_declaration"
            )
        {
            let mut cursor = node.walk();
            for declarator in node.children_by_field_name("declarator", &mut cursor) {
                if let Some(name) = name(declarator, source) {
                    names.push(name);
                }
            }
        } else if matches!(
            node.kind(),
            "struct_specifier" | "union_specifier" | "enum_specifier"
        ) && let Some(name) = name(node, source)
        {
            names.push(name);
        }
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            visit(child, source, names);
        }
    }
    let tree = parse(source)?;
    let mut names = Vec::new();
    visit(tree.root_node(), source, &mut names);
    Ok(names)
}

pub fn scopes(source: &str, tokens: &[Token]) -> Result<Vec<Scope>> {
    let tree = parse(source)?;
    let mut scopes = vec![Scope {
        owner: Owner {
            kind: "translation_unit".into(),
            name: "<file>".into(),
            context: Vec::new(),
        },
        start: 0,
        end: tokens.len(),
    }];
    collect(tree.root_node(), source, tokens, &[], &mut scopes)?;
    Ok(scopes)
}

fn matches(tokens: &[Token], start: usize, expected: &[String]) -> bool {
    tokens
        .get(start..start + expected.len())
        .is_some_and(|actual| {
            actual
                .iter()
                .zip(expected)
                .all(|(token, text)| &token.text == text)
        })
}

pub fn candidates(tokens: &[Token], scope: &Scope, site: &Site) -> Vec<usize> {
    (scope.start..=scope.end)
        .filter(|&i| {
            i >= scope.start + site.before.len()
                && i + site.replacement_tokens.len() + site.after.len() <= scope.end
                && (!site.at_start || i == scope.start + site.before.len())
                && (!site.at_end
                    || i + site.replacement_tokens.len() + site.after.len() == scope.end)
                && matches(tokens, i - site.before.len(), &site.before)
                && matches(tokens, i, &site.replacement_tokens)
                && matches(tokens, i + site.replacement_tokens.len(), &site.after)
        })
        .collect()
}

pub fn locate(
    tokens: &[Token],
    scopes: &[Scope],
    offset: usize,
    replacement: &str,
    kind: &str,
) -> Result<(Owner, Site)> {
    let index = tokens.partition_point(|token| token.end <= offset);
    let replacement_tokens = texts(&lex(replacement)?.tokens);
    let end = index + replacement_tokens.len();
    let scope = if kind == "top-level" {
        &scopes[0]
    } else {
        scopes
            .iter()
            .skip(1)
            .filter(|scope| scope.start <= index && end <= scope.end)
            .filter(|scope| {
                kind != "macro-body"
                    || (scope.start < index
                        && matches!(
                            scope.owner.kind.as_str(),
                            "preproc_def" | "preproc_function_def"
                        ))
            })
            .min_by_key(|scope| (usize::from(scope.end == index), scope.end - scope.start))
            .unwrap_or(&scopes[0])
    };
    let mut width = 8;
    let site = loop {
        let before_start = index.saturating_sub(width).max(scope.start);
        let after_end = (end + width).min(scope.end);
        let site = Site {
            kind: kind.into(),
            before: texts(&tokens[before_start..index]),
            after: texts(&tokens[end..after_end]),
            replacement_tokens: replacement_tokens.clone(),
            at_start: before_start == scope.start,
            at_end: after_end == scope.end,
            gap_before: String::new(),
            gap_after: String::new(),
        };
        if candidates(tokens, scope, &site).len() == 1 || width >= tokens.len() {
            break site;
        }
        width *= 2;
    };
    Ok((scope.owner.clone(), site))
}
