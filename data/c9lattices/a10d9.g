# Standard generators of A10 are a and b where a is in class 3A, b has order 9,
# ab has order 8 and abb has order 12.  Standard generators of the double
# cover 2.A10 are preimages A and B where A has order 3 and B has order 9.
# Irreducible, fixed by _LR.AI[1].

local _LR, a, b, A, B;
_LR := rec();
_LR.F := FreeGroup(2);

a := _LR.F.1;
b := _LR.F.2;
_LR.AI := [ [ a^-1, b*a^-1*Comm(a,b)^2 ] ];

A:=[[0,1,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0],
[1,0,0,0,0,0,0,0,0],
[0,0,0,1,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0],
[0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,1,0,0],
[0,0,0,0,0,0,0,1,0],
[0,0,0,0,0,0,0,0,1]];

B:=[[1,-1,0,0,0,0,0,0,0],
[0,-1,1,0,0,0,0,0,0],
[0,-1,0,1,0,0,0,0,0],
[0,-1,0,0,1,0,0,0,0],
[0,-1,0,0,0,1,0,0,0],
[0,-1,0,0,0,0,1,0,0],
[0,-1,0,0,0,0,0,1,0],
[0,-1,0,0,0,0,0,0,1],
[0,-1,0,0,0,0,0,0,0]];

_LR.G := GroupByGenerators([A,B]);

return _LR;