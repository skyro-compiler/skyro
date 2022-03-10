include config.mk

IDR_SRC = $(shell find ./src/ -name '*.idr')
LIB_SRC = $(shell find ./cairolib/ -name '*.idr')


# Builds the idrisToCairo compiler
$(IDRISCAIRO) : $(IDR_SRC) $(PACKAGE)
	$(IDRIS) --build $(PACKAGE)


.PHONY: clean
clean: clean-lib
	$(IDRIS) --clean $(PACKAGE)
	${MAKE} -C tests clean


.PHONY: build
build : $(IDRISCAIRO)


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


# run like: `make test only=test002`
.PHONY: test-only
test-only:
	${MAKE} -C tests only=$(only)


.PHONY: test
test: $(IDRISCAIRO) install-lib build-test test-only


int-tests:
	cd tests/idris-integer-types; \
	  pytest -vrPA test_intX_opt.py


docs:
	idris2 --mkdoc idrisToCairo.ipkg


docker-build:
	docker build . -t skyro
