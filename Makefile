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

# The previous memory model is still emitted and still has to keep working, so
# the suite runs a second time against it. Its output lives in `out_old/` and
# `_cache_old/`, so the two passes do not fight over a directory.
.PHONY: old-model-check
old-model-check: rust lib
	$(MAKE) -C test MODEL=old

.PHONY: palow-check
palow-check: rust lib
	./test/palow-check.sh

# Palow stores a scalar in the target's byte order, and the host is
# little-endian, so the suite runs once more translated for a big-endian
# target: 64-bit MIPS, whose C library headers Debian and Ubuntu package as
# libc6-dev-mips64-cross, under /usr/mips64-linux-gnuabi64. Every test the
# host's pass verifies must verify for it too, except one that names its own
# target, which the host's pass runs. Its output lives in
# `out.$(BIG_ENDIAN_TARGET)/`.
BIG_ENDIAN_TARGET ?= mips64-unknown-linux-gnuabi64
BIG_ENDIAN_SYSROOT ?= /usr/mips64-linux-gnuabi64

.PHONY: big-endian-check
big-endian-check: rust lib
	@test -f $(BIG_ENDIAN_SYSROOT)/include/stdlib.h || { \
		echo "big-endian-check: no C library headers under $(BIG_ENDIAN_SYSROOT)." >&2; \
		echo "Install libc6-dev-mips64-cross, or set BIG_ENDIAN_SYSROOT to a sysroot" >&2; \
		echo "for $(BIG_ENDIAN_TARGET)." >&2; \
		exit 1; }
	$(MAKE) -C test PAL_TARGET=$(BIG_ENDIAN_TARGET) PAL_SYSROOT=$(BIG_ENDIAN_SYSROOT)

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
test: rust lib -testsuite old-model-check big-endian-check
# Only run formatting checks when tests succeed
	$(MAKE) comment-check format-check

.PHONY: clean
clean:
	$(MAKE) -C test clean