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

.PHONY: format-check
format-check:
	cargo fmt --check
	clang-format --dry-run --Werror cpp/impl.cpp

.PHONY: test
test: rust lib -testsuite palow-check
# Only run formatting checks when tests succeed
	$(MAKE) format-check

.PHONY: clean
clean:
	$(MAKE) -C test clean