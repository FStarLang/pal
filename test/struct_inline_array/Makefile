.PHONY: all translate verify clean

C2PULSE ?= ../../target/debug/pal
FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE_DIR ?= _cache
OUT_DIR ?= out

C_FILES := $(wildcard *.c)
PAL_OPTS :=

# If there's an include/ directory, add -I include
ifneq ($(wildcard include),)
PAL_OPTS += -I include
endif

all: verify

translate: $(OUT_DIR)/.stamp

$(OUT_DIR)/.stamp: $(C_FILES) $(C2PULSE) pal.h
	@rm -rf $(OUT_DIR)
	@mkdir -p $(OUT_DIR)
	$(C2PULSE) $(PAL_OPTS) --outdir $(OUT_DIR) $(C_FILES)
	@touch $@

verify: $(OUT_DIR)/.stamp
	@$(MAKE) --no-print-directory -f ../verify.mk \
		OUT_DIR=$(OUT_DIR) FSTAR_EXE=$(FSTAR_EXE) CACHE_DIR=$(CACHE_DIR)

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR)
