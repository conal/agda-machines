all : html/Everything.html

MODULES:= \
  Mealy.agda \
  StreamFun.agda \
  VecFun.agda \
  SumIso.agda \

html/Everything.html: $(MODULES) Makefile
	@mkdir -p html
	agda -i. --html Everything.agda -v0

