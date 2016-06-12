
all: Common.vo Types.vo State.vo Syntax.vo Memory.vo UtilString.vo

Common.vo: Common.v
	coqc Common.v

Types.vo: Common.vo Types.v
	coqc Types.v

UtilString.vo: UtilString.v
	coqc UtilString.v

State.vo: Syntax.vo Common.vo Types.vo Memory.vo State.v
	coqc State.v

Memory.vo: Common.vo Types.vo Memory.v
	coqc Memory.v

Syntax.vo: Common.vo Types.vo Memory.vo UtilString.vo Syntax.v
	coqc Syntax.v

clean:
	rm *.vo *.glob
