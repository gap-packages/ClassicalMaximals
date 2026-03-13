# Standard generators of L2(11) are a and b where a has order 2, b has order 3
# and ab has order 11.
# Standard generators of the double cover 2.L2(11) = SL2(11) are preimages A and
# B where B has order 3 and AB has order 11.

local _LR, a, b, A, B;
_LR := rec();
_LR.F := FreeGroup(2);

a := _LR.F.1;
b := _LR.F.2;
_LR.AI := [ [a^-1, b^-1] ];

# irreducible, fixed by _LR.AI[1][1]

A:=[[0,1,0,0,0,0,0,0,0,-1],
[1,0,0,0,0,0,0,0,0,-1],
[0,0,0,1,0,0,0,0,0,-1],
[0,0,1,0,0,0,0,0,0,-1],
[0,0,0,0,0,0,1,0,0,-1],
[0,0,0,0,0,1,0,0,0,-1],
[0,0,0,0,1,0,0,0,0,-1],
[0,0,0,0,0,0,0,1,0,-1],
[0,0,0,0,0,0,0,0,1,-1],
[0,0,0,0,0,0,0,0,0,-1]];

B:=[[0,0,1,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[1,0,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,0,0,0,0,0,0,1,0],
[0,0,0,1,0,0,0,0,0,0],
[0,0,0,0,0,0,0,0,0,1],
[0,0,0,0,0,0,1,0,0,0]];

_LR.G := GroupByGenerators([A,B]);

return _LR;