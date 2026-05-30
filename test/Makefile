.PHONY: all clean

TESTS := $(shell find . -mindepth 1 -maxdepth 1 -type d \
	! -name '_*' ! -name '.*' | sort | sed 's|^\./||')

all: $(TESTS)

.PHONY: $(TESTS)
$(TESTS):
	@echo "=== $@ ==="
	@$(MAKE) -C $@

clean:
	@for d in $(TESTS); do $(MAKE) -C $$d clean; done
