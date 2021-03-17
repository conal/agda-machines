all : html/Everything.html

MODULES:= \
  Mealy.agda \
  StreamFun.agda \
  VecFun.agda \
  SumIso.agda \

html/Everything.html: $(MODULES)
	@mkdir -p html
	agda --html Everything.agda

