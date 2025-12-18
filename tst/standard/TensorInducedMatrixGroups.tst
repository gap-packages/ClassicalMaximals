gap> START_TEST("TensorInducedMatrixGroups.tst");

#
gap> TestTensorInducedDecompositionStabilizerInSL := function(m, t, q)
>   local G;
>   G := TensorInducedDecompositionStabilizerInSL(m, t, q);
>   CheckIsSubsetSL(m ^ t, q, G);
>   CheckSize(G);
> end;;
gap> TestTensorInducedDecompositionStabilizerInSL(3, 2, 5);
gap> TestTensorInducedDecompositionStabilizerInSL(2, 2, 7);
gap> TestTensorInducedDecompositionStabilizerInSL(2, 2, 5);
gap> TestTensorInducedDecompositionStabilizerInSL(3, 3, 3);

#
gap> TestTensorInducedDecompositionStabilizerInSU := function(m, t, q)
>   local G;
>   G := TensorInducedDecompositionStabilizerInSU(m, t, q);
>   CheckIsSubsetSU(m ^ t, q, G);
>   CheckSize(G);
> end;;
gap> TestTensorInducedDecompositionStabilizerInSU(2, 2, 7);
gap> TestTensorInducedDecompositionStabilizerInSU(2, 2, 5);
gap> TestTensorInducedDecompositionStabilizerInSU(3, 2, 3);
gap> TestTensorInducedDecompositionStabilizerInSU(3, 3, 3);
gap> TestTensorInducedDecompositionStabilizerInSU(3, 2, 5);

#
gap> TestTensorInducedDecompositionStabilizerInSp := function(m, t, q)
>   local G;
>   G := TensorInducedDecompositionStabilizerInSp(m, t, q);
>   CheckIsSubsetSp(m ^ t, q, G);
>   CheckSize(G);
> end;;
gap> TestTensorInducedDecompositionStabilizerInSp(2, 3, 7);
gap> TestTensorInducedDecompositionStabilizerInSp(4, 3, 3);
gap> TestTensorInducedDecompositionStabilizerInSp(2, 5, 3);

# Test error handling
gap> TensorInducedDecompositionStabilizerInSp(3, 3, 3);
Error, <m> must be even
gap> TensorInducedDecompositionStabilizerInSp(2, 2, 5);
Error, <t> must be odd
gap> TensorInducedDecompositionStabilizerInSp(2, 3, 4);
Error, <q> must be odd

#
gap> TestSymplecticTensorInducedDecompositionStabilizerInOmega := function(m, t, q)
>   local G;
>   G := SymplecticTensorInducedDecompositionStabilizerInOmega(m, t, q);
>   CheckIsSubsetOmega(1, m ^ t, q, G);
>   CheckSize(G);
> end;;
gap> TestSymplecticTensorInducedDecompositionStabilizerInOmega(2, 2, 5);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestSymplecticTensorInducedDecompositionStabilizerInOmega(2, 3, 8); # Error, !!!. See ./ReducibleMatrixGroups.tst for more info.
gap> TestSymplecticTensorInducedDecompositionStabilizerInOmega(2, 4, 5); # Error, List Element: <list>[3] must have an assigned value
#@fi
gap> TestSymplecticTensorInducedDecompositionStabilizerInOmega(4, 2, 3);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestSymplecticTensorInducedDecompositionStabilizerInOmega(4, 3, 2); # Error, This should never have happened (346), tell Max.
#@fi
gap> TestSymplecticTensorInducedDecompositionStabilizerInOmega(6, 2, 5);

# Test error handling
gap> SymplecticTensorInducedDecompositionStabilizerInOmega(3, 2, 3);
Error, <m> must be even
gap> SymplecticTensorInducedDecompositionStabilizerInOmega(4, 3, 3);
Error, <q> * <t> must be even
gap> SymplecticTensorInducedDecompositionStabilizerInOmega(4, 1, 2);
Error, <t> must be at least 2
gap> SymplecticTensorInducedDecompositionStabilizerInOmega(2, 2, 2);
Error, (<m>, <q>) = (2, 2) and (<m>, <q>) = (2, 3) are disallowed

#
gap> TestOrthogonalOddTensorInducedDecompositionStabilizerInOmega := function(m, t, q)
>   local G;
>   G := OrthogonalOddTensorInducedDecompositionStabilizerInOmega(m, t, q);
>   CheckIsSubsetOmega(0, m ^ t, q, G);
>   CheckSize(G);
> end;;
gap> TestOrthogonalOddTensorInducedDecompositionStabilizerInOmega(3, 2, 7);
gap> TestOrthogonalOddTensorInducedDecompositionStabilizerInOmega(3, 3, 5);
gap> TestOrthogonalOddTensorInducedDecompositionStabilizerInOmega(3, 4, 5);
gap> TestOrthogonalOddTensorInducedDecompositionStabilizerInOmega(5, 2, 5);
gap> TestOrthogonalOddTensorInducedDecompositionStabilizerInOmega(5, 3, 3);

# Test error handling
gap> OrthogonalOddTensorInducedDecompositionStabilizerInOmega(4, 2, 3);
Error, <m> must be odd
gap> OrthogonalOddTensorInducedDecompositionStabilizerInOmega(3, 2, 2);
Error, <q> must be odd
gap> OrthogonalOddTensorInducedDecompositionStabilizerInOmega(1, 2, 3);
Error, <m> must be at least 3
gap> OrthogonalOddTensorInducedDecompositionStabilizerInOmega(3, 1, 5);
Error, <t> must be at least 2
gap> OrthogonalOddTensorInducedDecompositionStabilizerInOmega(3, 2, 3);
Error, the case (<m>, <q>) = (3, 3) is disallowed

#
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega := function(epsilon, m, t, q)
>   local G;
>   G := OrthogonalEvenTensorInducedDecompositionStabilizerInOmega(epsilon, m, t, q);
>   CheckIsSubsetOmega(1, m ^ t, q, G);
>   CheckSize(G);
> end;;
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(-1, 4, 2, 3);
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(-1, 4, 2, 5);
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(-1, 4, 3, 3);
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(-1, 4, 2, 5);
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(1, 6, 2, 3);
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(1, 6, 2, 5);
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(-1, 6, 2, 3);
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(-1, 6, 2, 5);
gap> TestOrthogonalEvenTensorInducedDecompositionStabilizerInOmega(1, 8, 2, 3);

# Test error handling
gap> OrthogonalEvenTensorInducedDecompositionStabilizerInOmega(1, 5, 2, 3);
Error, <m> must be even
gap> OrthogonalEvenTensorInducedDecompositionStabilizerInOmega(1, 6, 2, 2);
Error, <q> must be odd
gap> OrthogonalEvenTensorInducedDecompositionStabilizerInOmega(1, 4, 2, 3);
Error, <m> must be at least 5 + <epsilon>
gap> OrthogonalEvenTensorInducedDecompositionStabilizerInOmega(1, 6, 1, 3);
Error, <t> must be at least 2

#
gap> STOP_TEST("TensorInducedMatrixGroups.tst", 0);
