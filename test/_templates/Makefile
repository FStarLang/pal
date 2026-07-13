.PHONY: all translate check verify compile clean

C2PULSE ?= ../../target/debug/pal
FSTAR_EXE ?= ../../opt/run-fstar.sh
CACHE_DIR ?= _cache
OUT_DIR ?= out
OBJ_DIR ?= obj

C_FILES := $(wildcard *.c)
H_FILES := $(wildcard *.h)
CHECKS := $(wildcard check-*.sh)
PAL_OPTS :=

# If there's an include/ directory, add -I include
ifneq ($(wildcard include),)
INCLUDES += -I include
endif
PAL_OPTS += $(INCLUDES)

all: check verify compile

check:
	@for check in $(CHECKS); do ./$$check; done

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
