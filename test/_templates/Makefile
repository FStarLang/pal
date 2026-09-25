.PHONY: all translate verify compile clean

# Palow is the memory model. The previous one is still here and still tested:
# `make MODEL=old` translates against it, into its own output and cache
# directories so that the two never overwrite each other's work. `out/` and
# `_cache/` belong to Palow, which is what an editor pointed at this directory
# finds.
MODEL ?= palow

C2PULSE ?= ../../target/debug/pal
CACHE_DIR ?= $(if $(filter old,$(MODEL)),_cache_old,_cache)
OUT_DIR ?= $(if $(filter old,$(MODEL)),out_old,out)
OBJ_DIR ?= obj

C_FILES := $(wildcard *.c)
H_FILES := $(wildcard *.h)
PAL_OPTS :=

ifeq ($(MODEL),old)
PAL_OPTS += --old-model
FSTAR_EXE ?= ../../opt/run-fstar.sh
# A helper module is written against a memory model, so a test whose helpers
# name Palow's predicates keeps a second copy under `helpers_palow/`. The C
# should not have to know which one it is getting, so the include path chooses.
HELPERS := helpers
else
# The Palow model's own modules are checked once, in `pulse/`, and found from
# there rather than re-verified in every test.
FSTAR_EXE ?= ../../opt/run-fstar.sh --include ../../pulse/_cache
HELPERS := $(if $(wildcard helpers_palow),helpers_palow,helpers)
endif

# If there's an include/ directory, add -I include
ifneq ($(wildcard include),)
INCLUDES += -I include
endif
PAL_OPTS += $(INCLUDES)

# A test whose annotations are written against the Palow memory model cannot be
# translated by the old emitter, and carries a `palow-only` marker file. Such a
# test is still compiled by a real C compiler -- the annotations must stay
# no-ops outside translation, which is the whole point of `pal.h` -- and is
# still verified under the default model. Only `MODEL=old` skips it.
ifeq ($(MODEL)$(wildcard palow-only),oldpalow-only)
all: compile
else
all: verify compile
endif

translate: $(OUT_DIR)/.stamp

$(OUT_DIR)/.stamp: $(C_FILES) $(H_FILES) $(C2PULSE) pal.h
	@mkdir -p $(OUT_DIR)
	$(C2PULSE) $(PAL_OPTS) --outdir $(OUT_DIR) $(C_FILES)
	@touch $@

verify: $(OUT_DIR)/.stamp
	@$(MAKE) --no-print-directory -f ../verify.mk \
		OUT_DIR=$(OUT_DIR) FSTAR_EXE="$(FSTAR_EXE)" CACHE_DIR=$(CACHE_DIR) \
		HELPERS=$(HELPERS) DEPEND=.depend.$(MODEL)

compile: $(patsubst %.c,$(OBJ_DIR)/%.o,$(C_FILES))

$(OBJ_DIR)/%.o: %.c $(C_FILES) $(H_FILES)
	@mkdir -p $(OBJ_DIR)
	$(CC) $(INCLUDES) -c $< -o $@

clean:
	rm -rf out _cache out_old _cache_old .depend.palow .depend.old $(OUT_DIR) $(CACHE_DIR) $(OBJ_DIR)
