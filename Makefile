all : tests
# all : listings

.PHONY: listings tests

# %: %.agda
# 	agda --compile $<

# Is there a build tool for Agda that tracks dependencies?

# Compile unconditionally
compile:
	agda --compile Test.agda

tests: Test
	./Test
	make -C figures

listings:
	@mkdir -p html
	agda -i. --html Everything.agda

