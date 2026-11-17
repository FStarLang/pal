.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE := _build/cache
OUT := _build/out
FILES := $(wildcard $(OUT)/*.fst $(OUT)/*.fsti theory/*.fst theory/*.fsti)
CHECKED := $(addprefix $(CACHE)/,$(addsuffix .checked,$(notdir $(FILES))))
FSTAR := $(FSTAR_EXE) --include ../../pulse/_cache \
	--include $(OUT) --include theory \
	--cache_checked_modules --cache_dir $(CACHE) \
	--already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore

.PHONY: all
all: $(CHECKED)

_build/verify.depend: $(FILES) verify.mk
	@mkdir -p $(CACHE)
	$(FSTAR) --dep full $(FILES) --output_deps_to $@

include _build/verify.depend

$(CACHE)/%.fst.checked:
	$(FSTAR) $<
	@touch -c $@

$(CACHE)/%.fsti.checked:
	$(FSTAR) $<
	@touch -c $@
