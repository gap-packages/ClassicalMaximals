# Standard generators of A9 are a and b where a is in class 3A, b has order 7,
# ab has order 9.  Standard generators of the double
# cover 2.A9 are preimages A and B where A has order 3 and B has order 7.
# Two constituents interchanged by _LR.AI[1].

local _LR, a, b, A, B;
_LR := rec();
_LR.F := FreeGroup(2);

a := _LR.F.1;
b := _LR.F.2;
_LR.AI := [ [ a^-1, b ] ];

# irreducible, mapped to inequivalent rep by auto
A:=[[-1,1,1,0,0,0,0,-1],
[0,0,0,0,-1,0,0,0],
[-1,0,0,-1,0,1,1,1],
[0,0,0,-1,-1,1,0,1],
[0,1,0,0,-1,0,0,0],
[0,1,0,0,0,-1,-1,-1],
[0,0,0,1,0,0,-1,-1],
[0,0,0,-1,-1,1,1,1]];

B:=[[0,0,1,-1,0,0,1,0],
[1,0,0,0,-1,0,0,0],
[0,-1,0,1,1,0,0,0],
[0,0,0,0,-1,1,0,1],
[1,-1,-1,0,0,-1,0,0],
[-1,0,0,-1,0,0,1,0],
[0,1,1,-1,-1,1,1,1],
[1,-1,-1,1,0,0,-1,0]];

_LR.G := GroupByGenerators([A,B]);

return _LR;