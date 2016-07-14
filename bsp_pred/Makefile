
all: Common.vo Types.vo State.vo Syntax.vo Memory.vo Operational.vo

Common.vo: Common.v
	coqc Common.v

Types.vo: Common.vo Types.v
	coqc Types.v

State.vo: Syntax.vo Common.vo Types.vo Memory.vo State.v
	coqc State.v

Memory.vo: Common.vo Types.vo Memory.v
	coqc Memory.v

Syntax.vo: Common.vo Types.vo Memory.vo  Syntax.v
	coqc Syntax.v

Operational.vo: Common.vo Syntax.vo Types.vo State.vo Memory.vo Operational.v
	coqc Operational.v

clean:
	rm *.vo *.glob
