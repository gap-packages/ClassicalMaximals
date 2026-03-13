local _LR, a, b, A, B;
_LR := rec();
_LR.F := FreeGroup(2);

a := _LR.F.1;
b := _LR.F.2;
_LR.AI := [ [ a^-1, b ] ];

# Standard generators of A11 are a and b where a is in class 3A, b has order 9,
# ab has order 11.  Standard generators of the double
# cover 2.A11 are preimages A and B where A has order 3 and B has order 9.
# Irreducible, fixed by _LR.AI[1].

A:=[[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0,0],
[1,0,0,0,0,0,0,0,0,0],
[0,0,0,1,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,0,0,0,0,0,0,1,0],
[0,0,0,0,0,0,0,0,0,1]];

B:=[[1,0,-1,0,0,0,0,0,0,0],
[0,1,-1,0,0,0,0,0,0,0],
[0,0,-1,1,0,0,0,0,0,0],
[0,0,-1,0,1,0,0,0,0,0],
[0,0,-1,0,0,1,0,0,0,0],
[0,0,-1,0,0,0,1,0,0,0],
[0,0,-1,0,0,0,0,1,0,0],
[0,0,-1,0,0,0,0,0,1,0],
[0,0,-1,0,0,0,0,0,0,1],
[0,0,-1,0,0,0,0,0,0,0]];

_LR.G := GroupByGenerators([A,B]);

return _LR;