# Standard generators of U4(2) = S4(3) are a, b where a is in class 2A,
# b has order 5 and ab has order 9.
# Standard generators of 2.U4(2) = Sp4(3) are preimages A,
# B where B has order 5 and AB has order 9.
local _LR, a, b, A, B;
_LR := rec();
_LR.F := FreeGroup(2);

a := _LR.F.1;
b := _LR.F.2;
_LR.AI := [ [a, b^-1] ];

# two constituents, interchanged by _LR.AI[1]
A:=[[1,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0],
[0,0,0,0,1,-1,1,0],
[0,0,1,-1,1,-1,1,0],
[0,0,0,0,0,0,0,1],
[0,0,0,0,1,-1,0,1],
[0,0,1,0,1,-1,0,0],
[0,0,0,0,1,0,0,0]];

B:=[[0,0,1,0,0,0,0,-1],
[0,0,1,-1,1,0,1,-1],
[0,-1,0,0,0,0,0,0],
[0,0,0,0,-1,1,0,-1],
[1,0,0,0,-1,1,0,-1],
[0,0,1,-1,0,0,1,-1],
[0,0,1,-1,0,0,0,-1],
[0,0,1,-1,1,-1,1,-1]];

_LR.G := GroupByGenerators([A,B]);

return _LR;