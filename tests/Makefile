INTERACTIVE ?= --interactive

.PHONY: test 
test: build
	./build/exec/runtests idris2 $(INTERACTIVE) --failure-file failures --only $(only)


.PHONY: retest
retest:
	@touch failures
	./build/exec/runtests idris2 $(INTERACTIVE) --failure-file failures --only-file failures --only $(only)


# We use idris2 to build the test runner.
.PHONY: build 
build: Main.idr tests.ipkg
	idris2 --build tests.ipkg


.PHONY: clean 
clean:
	find . -type d -name 'build' -prune -exec rm -rf {} \; ;\
	find . -type f -name 'output' -exec rm -rf {} \; ;\
	find . -type f -name '*.ttc' -exec rm -f {} \;
