all : listings

.PHONY: listings
listings:
	@mkdir -p html
	agda -i. --html Everything.agda

