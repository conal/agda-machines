all : tests
# all : listings

.PHONY: listings tests

tests:
	agda --compile Test.agda
	./Test
	make -C figures

listings:
	@mkdir -p html
	agda -i. --html Everything.agda

