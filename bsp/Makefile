
all: Common.vo Types.vo State.vo Syntax.vo Memory.vo UtilString.vo

Common.vo:
	coqc Common.v

Types.vo: Common.vo
	coqc Types.v

UtilString.vo:
	coqc UtilString.v

State.vo: Syntax.vo Common.vo Types.vo Memory.vo
	coqc State.v

Memory.vo: Common.vo Types.vo
	coqc Memory.v

Syntax.vo: Common.vo Types.vo Memory.vo UtilString.vo
	coqc Syntax.v

clean:
	rm *.vo *.glob
