.PHONY: all translate verify compile clean

C2PULSE ?= ../../target/debug/pal
FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE_DIR ?= _cache
OUT_DIR ?= out
OBJ_DIR ?= obj

C_FILES := $(wildcard *.c)
H_FILES := $(wildcard *.h)
PAL_OPTS :=

# If there's an include/ directory, add -I include
ifneq ($(wildcard include),)
INCLUDES += -I include
endif
PAL_OPTS += $(INCLUDES)

# A test whose annotations are written against the Palow memory model cannot be
# translated by the old emitter, and carries a `palow-only` marker file. Such a
# test is still compiled by a real C compiler -- the annotations must stay
# no-ops outside translation, which is the whole point of `pal.h` -- and is
# still checked by `test/palow-check.sh`. Only the old translator skips it.
ifneq ($(wildcard palow-only),)
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
		OUT_DIR=$(OUT_DIR) FSTAR_EXE=$(FSTAR_EXE) CACHE_DIR=$(CACHE_DIR)

compile: $(patsubst %.c,$(OBJ_DIR)/%.o,$(C_FILES))

$(OBJ_DIR)/%.o: %.c $(C_FILES) $(H_FILES)
	@mkdir -p $(OBJ_DIR)
	$(CC) $(INCLUDES) -c $< -o $@

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR) $(OBJ_DIR)
