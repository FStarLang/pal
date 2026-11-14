# Auxiliary makefile for F* verification.
# Invoked from per-test Makefiles with:
#   OUT_DIR   — directory containing .fst/.fsti files
#   FSTAR_EXE — path to the F* runner script
#   CACHE_DIR — directory for .fst.checked files

FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE_DIR  ?= _cache
OUT_DIR    ?= out
EXPECTED_FAILURES_FILE ?=
EXPECTED_FAILURE_TEXT_FILE ?=

FSTAR = $(FSTAR_EXE) \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore \
	--include $(OUT_DIR)

# Optional wall-clock bound per Z3 query, in milliseconds (e.g.
# `make Z3_TIMEOUT_MS=300000`). Z3's rlimit does not bound wall time (some
# quantifier loops run for hours on a few rlimit units); an expired query is
# reported as an ordinary F* Error 19 "The SMT query timed out". The bound
# applies per check-sat, so fuel/ifuel retries multiply it.
Z3_TIMEOUT_MS ?=
ifneq ($(Z3_TIMEOUT_MS),)
FSTAR += --z3cliopt timeout=$(Z3_TIMEOUT_MS)
endif

# Which directory of hand-written F* this test ships, if any.
HELPERS ?= helpers
ifneq ($(wildcard $(HELPERS)),)
FSTAR += --include $(HELPERS)
endif

FST_FILES := $(wildcard $(OUT_DIR)/*.fst)
FSTI_FILES := $(wildcard $(OUT_DIR)/*.fsti)
EXPECTED_FAILURE_MODULES := $(if $(wildcard $(EXPECTED_FAILURES_FILE)),$(shell sed 's/#.*//; /^[[:space:]]*$$/d; s/[[:space:]]//g; s/\.fst$$//' $(EXPECTED_FAILURES_FILE)))
EXPECTED_FAILURE_FILES := $(addprefix $(OUT_DIR)/,$(addsuffix .fst,$(EXPECTED_FAILURE_MODULES)))
ALL_CHECKED_FILES := $(patsubst $(OUT_DIR)/%.fst,$(CACHE_DIR)/%.fst.checked,$(filter-out $(EXPECTED_FAILURE_FILES),$(FST_FILES))) \
                     $(patsubst $(OUT_DIR)/%.fsti,$(CACHE_DIR)/%.fsti.checked,$(FSTI_FILES))

.PHONY: all
all: $(ALL_CHECKED_FILES) expected-verification-failures

.PHONY: expected-verification-failures
expected-verification-failures: $(ALL_CHECKED_FILES)
	@for m in $(EXPECTED_FAILURE_MODULES); do \
		echo "Expecting verification failure $$m.fst"; \
		test -f "$(OUT_DIR)/$$m.fst" || exit 1; \
		if $(FSTAR) $(OUT_DIR)/$$m.fst >$(CACHE_DIR)/$$m.expected-failure.log 2>&1; then \
			echo "ERROR: $$m.fst unexpectedly verified"; exit 1; \
		fi; \
		if test -f "$(EXPECTED_FAILURE_TEXT_FILE)" && \
			! grep -F -q -f "$(EXPECTED_FAILURE_TEXT_FILE)" $(CACHE_DIR)/$$m.expected-failure.log; then \
			cat $(CACHE_DIR)/$$m.expected-failure.log; exit 1; \
		fi; \
	done

$(shell mkdir -p $(CACHE_DIR))

DEPEND ?= .depend

$(DEPEND): $(FST_FILES) $(FSTI_FILES)
	$(FSTAR) --dep full $(FST_FILES) $(FSTI_FILES) --output_deps_to $@

include $(DEPEND)

$(CACHE_DIR)/%.fst.checked:
	@echo "Verifying $*.fst"
	$(FSTAR) $<
	@touch -c $@

$(CACHE_DIR)/%.fsti.checked:
	@echo "Verifying $*.fsti"
	$(FSTAR) $<
	@touch -c $@

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR) $(DEPEND)
