.PHONY: all
all: rust lib

.PHONY: rust
rust:
	cargo build

.PHONY: lib
lib:
	$(MAKE) -C pulse

.PHONY: -testsuite
-testsuite: rust lib
	$(MAKE) -C test

.PHONY: palow-check
palow-check: rust lib
	./test/palow-check.sh

.PHONY: comment-check
# F* comments nest and quoted C code is full of accidental delimiters, so an
# unbalanced comment silently swallows the rest of a file rather than failing.
comment-check:
	./opt/check-comments.py pulse/*.fst pulse/*.fsti

.PHONY: format-check
format-check:
	cargo fmt --check
	clang-format --dry-run --Werror cpp/impl.cpp

.PHONY: test
test: rust lib -testsuite
# Only run formatting checks when tests succeed
	$(MAKE) comment-check format-check

.PHONY: clean
clean:
	$(MAKE) -C test clean

# Binary package: dist/pal-<version>-<commit>-linux-<arch>.tar.gz. See
# opt/package.sh for PACKAGE_OPTS (e.g. --check-pulse, --llvm system,
# --fstar DIR, --fstar-ref REF).
PACKAGE_OPTS ?=
.PHONY: package
package:
	./opt/package.sh --out dist $(PACKAGE_OPTS)

# Smoke-test the most recent package (run `make package` first).
.PHONY: package-test
package-test:
	./opt/package-test.sh $$(ls -t dist/pal-*.tar.gz dist/pal-*.zip 2>/dev/null | head -1)
