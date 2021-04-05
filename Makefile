all : tests

.PHONY: listings tests

# %: %.agda
# 	agda --compile $<

# Is there a build tool for Agda that tracks dependencies?

# Compile unconditionally
Test:
	agda --compile TestB.agda

compile: TestB

tests: TestB
	./TestB
	make -C Figures

listings:
	@mkdir -p html
	agda -i. --html Everything.agda


clean:
	rm -rf Test html
