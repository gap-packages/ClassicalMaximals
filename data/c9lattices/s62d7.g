# Standard generators of S6(2) are a and b where a is in class 2A, b has order 7
# and ab has order 9.  Standard generators of the double cover 2.S6(2) are
# preimages A and B where B has order 7 and AB has order 9.  

local _LR, a, b, A, B;
_LR := rec();
_LR.F := FreeGroup(2);

_LR.AI := [ ];
# irreducible

A:=[[-1,0,0,0,0,0,0],
[0,-1,0,0,0,0,0],
[0,0,-1,0,0,0,0],
[0,0,-1,1,1,-1,-1],
[0,0,0,0,-1,0,0],
[0,0,0,0,0,-1,0],
[0,0,0,0,0,0,-1]];

B:=[[0,0,0,1,0,0,0],
[0,1,-1,0,1,-1,0],
[0,1,-1,0,1,0,0],
[0,0,0,0,1,0,0],
[0,0,-1,1,0,0,0],
[0,0,0,0,0,0,1],
[1,0,0,0,0,0,0]];

_LR.G := GroupByGenerators([A,B]);

return _LR;