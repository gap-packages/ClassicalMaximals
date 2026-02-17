# Standard generators of M12 are a and b where a is in class 2B, b is in class
# 3B and ab has order 11.
# Standard generators of the double cover 2.M12 are preimages A and B where A is
# in class +2B, B has order 6 and AB has order 11. (Note that any two of these
# conditions imply the third.)

local _LR, a, b, A, B;
_LR := rec();
_LR.F := FreeGroup(2);

a := _LR.F.1;
b := _LR.F.2;
_LR.AI := [ [a, a*b^-1*a ] ];

# irreducible, mapped to inequivalent rep by _LR.AI[1]

A:=[[1,0,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0,0],
[0,0,0,1,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0,0],
[0,0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,0,0,1,0],
[0,0,0,0,0,0,0,0,1,0,0],
[-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1]];

B:=[[0,1,0,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0,0,0],
[1,0,0,0,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0,0],
[0,0,0,1,0,0,0,0,0,0,0],
[0,0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,0,1,0,0],
[0,0,0,0,0,0,1,0,0,0,0],
[0,0,0,0,0,0,0,0,0,0,1],
[-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1]];

_LR.G := GroupByGenerators([A,B]);

return _LR;