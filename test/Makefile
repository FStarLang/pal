.PHONY: all
all: verify

TESTS := $(filter-out $(EXPECTED_FAIL),$(wildcard *.c))

CACHE_DIR ?= _cache

C2PULSE ?= ../target/debug/pal

# Tests that are expected to fail (known unsupported features)
EXPECTED_FAIL :=

# Per-test pal options (e.g., OPTS_include = -I include)
OPTS_include = -I include

# Each .c file produces output in its own subdirectory (out/<stem>/)
OUT_DIR := out
$(shell mkdir -p $(OUT_DIR))

ALL_STAMPS := $(patsubst %.c,$(OUT_DIR)/%/.stamp,$(TESTS))

# Generate per-file rules for translation
define make_stamp_rule
$(OUT_DIR)/$(1:.c=)/.stamp: $(1) $$(C2PULSE) pal.h
	@mkdir -p $(OUT_DIR)/$(1:.c=)
	$$(C2PULSE) $$(OPTS_$(basename $(1))) --outdir $(OUT_DIR)/$(1:.c=) $(1)
	@touch $$@
endef
$(foreach t,$(TESTS),$(eval $(call make_stamp_rule,$(t))))

.PHONY: translate
translate: $(ALL_STAMPS)

# ── Verification ───────────────────────────────────────────────────
# Each test gets its own verify target that invokes verify.mk in its output dir.

FSTAR_EXE ?= ../opt/run-fstar.sh

TEST_STEMS   := $(patsubst %.c,%,$(TESTS))
VERIFY_TARGETS := $(patsubst %,verify-%,$(TEST_STEMS))

.PHONY: verify $(VERIFY_TARGETS)
verify: $(VERIFY_TARGETS)

$(VERIFY_TARGETS): verify-%: $(OUT_DIR)/%/.stamp
	@$(MAKE) -C $(OUT_DIR)/$* -f ../../verify.mk \
		FSTAR_EXE=../../$(FSTAR_EXE) \
		CACHE_DIR=../../$(CACHE_DIR)/$*

.PHONY: clean
clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR)

# ── Expected-fail targets ──────────────────────────────────────────
# Run with: make test-expected-fail
.PHONY: test-expected-fail
test-expected-fail: $(patsubst %.c,test-xfail-%,$(EXPECTED_FAIL))

test-xfail-%: %.c $(C2PULSE)
	@echo "=== Expected failure: $< ==="
	@output=$$($(C2PULSE) $< 2>&1); \
	if echo "$$output" | grep -q "^error:"; then \
	  echo "$$output"; \
	  echo "OK — got expected error"; \
	else \
	  echo "$$output"; \
	  echo "UNEXPECTED PASS — $< should have failed"; exit 1; \
	fi

