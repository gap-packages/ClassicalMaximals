gap> TestClassicalMaximalsLinear := function(args)
>   return Length(ClassicalMaximalsGeneric("L", args[1], args[2])) = args[3];
> end;;
gap> testsClassicalMaximalsLinear := [[2, 4, 3], [2, 5, 3], [2, 7, 3],
>                                     [2, 8, 3], [2, 9, 3], [2, 11, 2],
>                                     [2, 13, 4], [2, 16, 4], [2, 17, 5],
>                                     [2, 19, 3],
>                                     [3, 2, 3], [3, 3, 4], [3, 4, 6],
>                                     [3, 5, 5], [3, 7, 8], [3, 8, 5],
>                                     [3, 9, 7], [3, 11, 5], [3, 13, 8],
>                                     [3, 16, 8], [3, 17, 5], [3, 19, 10],
>                                     [4, 2, 5], [4, 3, 8], [4, 4, 8],
>                                     [4, 5, 13], [4, 7, 10], [4, 8, 8],
>                                     [4, 9, 18], [4, 11, 10], [4, 13, 14],
>                                     [4, 16, 9], [4, 17, 16], [4, 19, 10]];;
gap> ForAll(testsClassicalMaximalsLinear, TestClassicalMaximalsLinear);
true
gap> TestClassicalMaximalsUnitary := function(args)
>   return Length(ClassicalMaximalsGeneric("U", args[1], args[2])) = args[3];
> end;;
gap> testsClassicalMaximalsUnitary := [[3, 3, 3], [3, 4, 4], [3, 5, 2], 
>                                      [3, 7, 5], [3, 8, 7], [3, 9, 5], 
>                                      [3, 11, 8], [3, 13, 5], [3, 16, 4],
>                                      [3, 17, 10], [3, 19, 5],
>                                      [4, 2, 5], [4, 3, 10], [4, 4, 7],
>                                      [4, 5, 10], [4, 7, 16], [4, 8, 8],
>                                      [4, 9, 10], [4, 11, 14], [4, 13, 10],
>                                      [4, 16, 7], [4, 17, 10], [4, 19, 14],
>                                      [5, 2, 5], [5, 3, 7], [5, 4, 11], 
>                                      [5, 5, 7], [5, 7, 7], [5, 8, 7],
>                                      [5, 9, 16], [5, 11, 7], [5, 13, 7], 
>                                      [5, 16, 6], [5, 17, 7], [5, 19, 16],
>                                      [6, 2, 10], [6, 3, 14], [6, 4, 12],
>                                      [6, 5, 20], [6, 7, 14], [6, 8, 17],
>                                      [7, 2, 8], [7, 3, 9], [7, 8, 9],
>                                      [7, 13, 22],
>                                      [8, 2, 11], [8, 3, 25], [8, 4, 13],
>                                      [8, 5, 17], [8, 8, 14],
>                                      [9, 2, 14], [9, 3, 13], [9, 4, 12],
>                                      [9, 5, 20], [9, 8, 17],
>                                      [10, 2, 14], [10, 3, 18],
>                                      [11, 2, 12], [11, 3, 13],
>                                      [12, 2, 21], [12, 3, 27]];;
gap> ForAll(testsClassicalMaximalsUnitary, TestClassicalMaximalsUnitary);
true
