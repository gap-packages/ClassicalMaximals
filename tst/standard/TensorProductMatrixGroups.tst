gap> START_TEST("TensorProductMatrixGroups.tst");

#
gap> TestTensorProductStabilizerInSL := function(d1, d2, q)
>   local G;
>   G := TensorProductStabilizerInSL(d1, d2, q);
>   CheckIsSubsetSL(d1 * d2, q, G);
>   CheckSize(G);
> end;;
gap> TestTensorProductStabilizerInSL(2, 3, 2);
gap> TestTensorProductStabilizerInSL(2, 3, 3);
gap> TestTensorProductStabilizerInSL(2, 3, 4);
gap> TestTensorProductStabilizerInSL(2, 3, 5);
gap> TestTensorProductStabilizerInSL(2, 4, 3);
gap> TestTensorProductStabilizerInSL(3, 4, 2);
gap> TestTensorProductStabilizerInSL(3, 4, 3);

#
gap> TestTensorProductStabilizerInSU := function(d1, d2, q)
>   local G;
>   G := TensorProductStabilizerInSU(d1, d2, q);
>   CheckIsSubsetSU(d1 * d2, q, G);
>   CheckSize(G);
> end;;
gap> TestTensorProductStabilizerInSU(2, 3, 2);
gap> TestTensorProductStabilizerInSU(2, 3, 3);
gap> TestTensorProductStabilizerInSU(2, 3, 4);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestTensorProductStabilizerInSU(2, 4, 3); # FIXME: see https://github.com/gap-packages/recog/issues/302
#@fi

#
gap> TestTensorProductStabilizerInSp := function(epsilon, d1, d2, q)
>   local G;
>   G := TensorProductStabilizerInSp(epsilon, d1, d2, q);
>   CheckIsSubsetSp(d1 * d2, q, G);
>   CheckSize(G);
> end;;
gap> TestTensorProductStabilizerInSp(0, 2, 3, 3);
gap> TestTensorProductStabilizerInSp(0, 4, 3, 5);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestTensorProductStabilizerInSp(1, 2, 4, 5);  # FIXME: see https://github.com/gap-packages/recog/issues/316
#@fi
gap> TestTensorProductStabilizerInSp(-1, 2, 4, 5);

# Test error handling
gap> TensorProductStabilizerInSp(0, 1, 3, 3);
Error, <d1> must be even
gap> TensorProductStabilizerInSp(0, 2, 3, 2);
Error, <q> must be odd
gap> TensorProductStabilizerInSp(0, 2, 2, 3);
Error, <d2> must be at least 3
gap> TensorProductStabilizerInSp(1, 2, 3, 3);
Error, <epsilon> must be 0 since <d2> is odd
gap> TensorProductStabilizerInSp(0, 2, 4, 3);
Error, <epsilon> must be +1 or -1 since <d2> is even

#
gap> TestOrthogonalTensorProductStabilizerInOmega := function(epsilon, epsilon_1, epsilon_2, d1, d2, q)
>   local G;
>   G := OrthogonalTensorProductStabilizerInOmega(epsilon, epsilon_1, epsilon_2, d1, d2, q);
>   CheckIsSubsetOmega(epsilon, d1 * d2, q, G);
>   CheckSize(G);
> end;;
gap> TestOrthogonalTensorProductStabilizerInOmega(0, 0, 0, 3, 5, 5);
gap> TestOrthogonalTensorProductStabilizerInOmega(-1, -1, 0, 4, 3, 5);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, 1, 0, 4, 3, 5);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, 1, 1, 4, 6, 3);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, 1, -1, 4, 6, 3);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, 1, -1, 6, 4, 3);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, -1, -1, 4, 6, 3);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, 1, 1, 4, 6, 5);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, 1, -1, 4, 6, 5);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, 1, -1, 6, 4, 5);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, -1, -1, 4, 6, 5);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, 1, 1, 6, 8, 3);
gap> TestOrthogonalTensorProductStabilizerInOmega(1, -1, -1, 6, 10, 3);

# Test error handling
gap> OrthogonalTensorProductStabilizerInOmega(1, 1, 1, 4, 6, 2);
Error, <q> must be odd
gap> OrthogonalTensorProductStabilizerInOmega(0, 0, 0, 5, 5, 3);
Error, [<epsilon_1>, <d1>] must not be equal to [<epsilon_2>, <d2>]
gap> OrthogonalTensorProductStabilizerInOmega(1, 1, 1, 2, 4, 3);
Error, <d1> and <d2> must be at least 3
gap> OrthogonalTensorProductStabilizerInOmega(0, 0, 0, 4, 5, 3);
Error, <d1> must be odd
gap> OrthogonalTensorProductStabilizerInOmega(1, 1, 1, 5, 6, 3);
Error, <d1> must be even
gap> OrthogonalTensorProductStabilizerInOmega(1, 2, 1, 4, 6, 3);
Error, <epsilon_1> must be in [-1, 0, 1]
gap> OrthogonalTensorProductStabilizerInOmega(0, 0, 0, 5, 6, 3);
Error, <d2> must be odd
gap> OrthogonalTensorProductStabilizerInOmega(1, 1, 1, 4, 5, 3);
Error, <d2> must be even
gap> OrthogonalTensorProductStabilizerInOmega(1, 1, 2, 4, 6, 3);
Error, <epsilon_2> must be in [-1, 0, 1]
gap> OrthogonalTensorProductStabilizerInOmega(0, 1, 1, 4, 6, 3);
Error, <d> must be odd
gap> OrthogonalTensorProductStabilizerInOmega(1, 0, 0, 5, 7, 3);
Error, <d> must be even
gap> OrthogonalTensorProductStabilizerInOmega(2, 1, 1, 4, 6, 3);
Error, <epsilon> must be in [-1, 0, 1]
gap> OrthogonalTensorProductStabilizerInOmega(1, 0, 1, 5, 6, 3);
Error, <epsilon2> must be 0 if <epsilon_1> is 0]
gap> OrthogonalTensorProductStabilizerInOmega(1, -1, 1, 4, 6, 3);
Error, by symmetry, we disallow this case
gap> OrthogonalTensorProductStabilizerInOmega(1, 1, 1, 6, 4, 3);
Error, by symmetry, we assume d1 < d2 in this case
gap> OrthogonalTensorProductStabilizerInOmega(1, -1, 0, 4, 5, 3);
Error, <epsilon> = -1 must be equivalent to <epsilon_1> = -1 and <epsilon_2> =\
 0

#
gap> TestSymplecticTensorProductStabilizerInOmega := function(d1, d2, q)
>   local G;
>   G := SymplecticTensorProductStabilizerInOmega(d1, d2, q);
>   CheckIsSubsetOmega(1, d1 * d2, q, G);
>   CheckSize(G);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestSymplecticTensorProductStabilizerInOmega(2, 4, 8); # Error, !!!. See ./ReducibleMatrixGroups.tst for more info and examples
#@fi
gap> TestSymplecticTensorProductStabilizerInOmega(2, 4, 7);
gap> TestSymplecticTensorProductStabilizerInOmega(2, 6, 4);
gap> TestSymplecticTensorProductStabilizerInOmega(2, 6, 5);
gap> TestSymplecticTensorProductStabilizerInOmega(2, 8, 2);
gap> TestSymplecticTensorProductStabilizerInOmega(2, 8, 3);

# Test error handling
gap> SymplecticTensorProductStabilizerInOmega(2, 3, 5);
Error, <d1> and <d2> must be even
gap> SymplecticTensorProductStabilizerInOmega(4, 2, 5);
Error, <d1> must be less than <d2>

#
gap> STOP_TEST("TensorProductMatrixGroups.tst", 0);
