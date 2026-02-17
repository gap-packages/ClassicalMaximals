local _LR, a, b, A, B;
_LR := rec();
_LR.F := FreeGroup(2);

a := _LR.F.1;
b := _LR.F.2;
_LR.AI := [ [a, a*b*b*a*b*a*b*b] ];

# two consitutents interchanged by _LR.AI[1]

A:=[[-1,0,0,0,0,0],
[0,0,0,0,1,0],
[0,0,0,1,0,0],
[0,0,1,0,0,0],
[0,1,0,0,0,0],
[0,0,0,0,0,-1]];

B:=[[-1,1,-1,0,0,0],
[-1,0,0,0,0,0],
[0,0,1,0,0,0],
[-1,0,0,1,-1,0],
[0,0,1,0,-1,1],
[0,0,0,0,-1,0]];

_LR.G := GroupByGenerators([A,B]);

return _LR;