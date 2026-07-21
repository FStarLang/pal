# Self-contained build/verify Makefile for the function-pointer workspace.
#
#   make translate              translate func_pointer.c -> out/*.fst(i)
#   make verify                 translate, then verify every generated module
#   make verify-one MODULE=Func_swap
#                               translate, then verify a single module
#                               (its dependencies are built first, in order)
#   make clean                  remove out/, _cache/ and .depend
#
# Paths are relative to this directory (one level below the repo root).

PAL       ?= ../target/debug/pal
FSTAR_EXE ?= ../opt/run-fstar.sh
OUT_DIR   ?= out
CACHE_DIR ?= _cache

C_FILES := $(wildcard *.c)

FSTAR = $(FSTAR_EXE) \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore \
	--include $(OUT_DIR)

.PHONY: all translate verify verify-all verify-one clean _verify _verify_one

all: verify

# --- Translation -----------------------------------------------------------

translate: $(OUT_DIR)/.stamp

$(OUT_DIR)/.stamp: $(C_FILES) $(PAL) pal.h
	@mkdir -p $(OUT_DIR)
	$(PAL) --outdir $(OUT_DIR) $(C_FILES)
	@touch $@

# --- Verification ----------------------------------------------------------
# The .fst files are produced by `translate`, so the wildcards that enumerate
# them (below) must be evaluated in a *second* make pass, after translation.
# The public targets therefore recurse into the `_verify*` helper targets.

verify verify-all: translate
	@$(MAKE) --no-print-directory _verify

# Verify a single module, e.g.  make verify-one MODULE=Func_swap
# Dependencies are resolved through .depend, so they are checked first.
verify-one: translate
	@if [ -z "$(MODULE)" ]; then \
		echo "usage: make verify-one MODULE=<ModuleName>"; exit 2; fi
	@$(MAKE) --no-print-directory _verify_one MODULE=$(MODULE)

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR) .depend

# ---------------------------------------------------------------------------
# Second-pass machinery: at this point out/*.fst(i) exist and resolve.
# ---------------------------------------------------------------------------

FST_FILES   := $(wildcard $(OUT_DIR)/*.fst)
FSTI_FILES  := $(wildcard $(OUT_DIR)/*.fsti)
ALL_CHECKED := $(patsubst $(OUT_DIR)/%.fst,$(CACHE_DIR)/%.fst.checked,$(FST_FILES)) \
               $(patsubst $(OUT_DIR)/%.fsti,$(CACHE_DIR)/%.fsti.checked,$(FSTI_FILES))

_verify: $(ALL_CHECKED)
	@echo "All modules verified."

_verify_one: $(CACHE_DIR)/$(MODULE).fst.checked
	@echo "$(MODULE) verified."

$(shell mkdir -p $(CACHE_DIR))

# Dependency graph among the generated modules (drives build ordering and
# supplies each %.checked rule's source .fst via $<).
.depend: $(FST_FILES) $(FSTI_FILES)
	$(FSTAR) --dep full $(FST_FILES) $(FSTI_FILES) --output_deps_to $@

# Only pull in .depend once the generated files exist (i.e. in the second
# pass); otherwise the first pass would needlessly try to build it empty.
ifneq ($(strip $(FST_FILES)$(FSTI_FILES)),)
-include .depend
endif

$(CACHE_DIR)/%.fst.checked:
	@echo "Verifying $*.fst"
	$(FSTAR) $<
	@touch -c $@

$(CACHE_DIR)/%.fsti.checked:
	@echo "Verifying $*.fsti"
	$(FSTAR) $<
	@touch -c $@
