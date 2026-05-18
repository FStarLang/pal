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

# Generate per-file rules
define make_stamp_rule
$(OUT_DIR)/$(1:.c=)/.stamp: $(1) $$(C2PULSE) pal.h
	@mkdir -p $(OUT_DIR)/$(1:.c=)
	$$(C2PULSE) $$(OPTS_$(basename $(1))) --outdir $(OUT_DIR)/$(1:.c=) $(1)
	@touch $$@
endef
$(foreach t,$(TESTS),$(eval $(call make_stamp_rule,$(t))))

.PHONY: translate
translate: $(ALL_STAMPS)

# Verification: after translation, verify each test's .fst files
FSTAR_EXE ?= ../opt/run-fstar.sh
FSTAR = $(FSTAR_EXE) \
	--cache_checked_modules	\
	--cache_dir $(CACHE_DIR) \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore

.PHONY: verify
verify: translate
	@failed=0; \
	for dir in $(OUT_DIR)/*/; do \
		test_name=$$(basename "$$dir"); \
		cache_dir="$(CACHE_DIR)/$$test_name"; \
		mkdir -p "$$cache_dir"; \
		for f in $$(find "$$dir" -maxdepth 1 -name '*.fst' | sort); do \
			base=$$(basename $$f .fst); \
			if [ ! -f "$$cache_dir/$$base.fst.checked" ]; then \
				echo "Verifying $$f"; \
				if ! $(FSTAR_EXE) --cache_checked_modules --cache_dir "$$cache_dir" --already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore --include "$$dir" $$f; then \
					failed=$$((failed + 1)); \
				fi; \
			fi; \
		done; \
	done; \
	if [ $$failed -gt 0 ]; then \
		echo "$$failed module(s) failed verification"; \
		exit 1; \
	fi

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
