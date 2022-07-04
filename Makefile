include config.mk

IDR_SRC = $(shell find ./src/ -name '*.idr')
LIB_SRC = $(shell find ./cairolib/ -name '*.idr')


# Builds the idrisToCairo compiler
$(IDRISCAIRO) : $(IDR_SRC) $(PACKAGE)
	$(IDRIS) --build $(PACKAGE)

# Builds the skyroToCairo compiler
$(SKYROCAIRO) : $(IDR_SRC) $(PACKAGE_SKYRO)
	$(IDRIS) --build $(PACKAGE_SKYRO)


.PHONY: clean
clean: clean-lib
	$(IDRIS) --clean $(PACKAGE)
	$(IDRIS) --clean $(PACKAGE_SKYRO)
	${MAKE} -C tests clean


.PHONY: build
build : $(IDRISCAIRO) $(SKYROCAIRO)


# Skyro library
.PHONY: build-lib
build-lib : build $(LIB_SRC) ./cairolib/cairolib.ipkg
	$(IDRISCAIRO) --build ./cairolib/cairolib.ipkg


.PHONY: install-lib
install-lib : build-lib
	$(IDRISCAIRO) --install ./cairolib/cairolib.ipkg


.PHONY: clean-lib
clean-lib : 
	$(IDRIS) --clean ./cairolib/cairolib.ipkg


# Tests
.PHONY: build-test
build-test: 
	@${MAKE} -C tests build

.PHONY: run-example
run-example: install-lib Example.idr
	[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate ; \
	$(IDRISCAIRO) --no-prelude -p cairolib --cg cairo --directive verbose Example.idr -o Example.cairo_unformatted && \
	cairo-format $(BUILDDIR)/Example.cairo_unformatted > $(BUILDDIR)/Example.cairo && \
	cairo-compile $(BUILDDIR)/Example.cairo --cairo_path ./skyro-runtime --output $(BUILDDIR)/Example_compile.json && \
	cairo-run --program=$(BUILDDIR)/Example_compile.json --print_output --print_info --layout=small

.PHONY: run-example
run-example-skyro: install-lib Example.skyro
	[ -f ~/cairo_venv/bin/activate ] && source ~/cairo_venv/bin/activate ; \
	$(SKYROCAIRO) --verbose --input Example.skyro --output $(BUILDDIR)/Example.cairo_unformatted && \
	cairo-format $(BUILDDIR)/Example.cairo_unformatted > $(BUILDDIR)/Example.cairo && \
	cairo-compile $(BUILDDIR)/Example.cairo --cairo_path ./skyro-runtime --output $(BUILDDIR)/Example_compile.json && \
	cairo-run --program=$(BUILDDIR)/Example_compile.json --print_output --print_info --layout=small

# run like: `make test only=test002`
.PHONY: test-only
test-only:
	${MAKE} -C tests only=$(only)


.PHONY: test
test: $(IDRISCAIRO) $(SKYROCAIRO) install-lib build-test test-only


int-tests:
	cd tests/idris-integer-types; \
	  pytest -vrPA test_intX_opt.py


docs:
	idris2 --mkdoc idrisToCairo.ipkg


docker-build:
	docker build . -t skyro
