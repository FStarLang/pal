## Summary

- Add an optional stdio MCP server via `cargo build --features mcp` and `pal mcp`, leaving the default CLI unchanged.
- Add project switching with `new_root`, session management, and include-path/preprocessor-definition tools. Root changes cancel previous work and clear sessions/caches; compiler-option changes invalidate proof caches.
- Support incremental C verification with F*/Pulse proof reuse and a bounded exact-result LRU, preserving the last accepted revision on failure or cancellation.
- Expose Clang-based definitions, references, callers/callees, symbols and hover, plus subscribable verification status and diagnostics.

## Verification

- Real MCP integration coverage for incremental proofs, cache invalidation, navigation, project switching and cancellation.
- `LIBCLANG_PATH=/usr/lib/llvm20/lib cargo test --features mcp -- --nocapture`
- `env -u ADMIT -u OTHERFLAGS make test -j8`
