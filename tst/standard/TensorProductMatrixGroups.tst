gap> START_TEST("TensorProductMatrixGroups.tst");

#
gap> TestTensorProductStabilizerInSL := function(d1, d2, q)
>   local G;
>   G := TensorProductStabilizerInSL(d1, d2, q);
>   CheckSize(G);
>   CheckIsSubsetSL(d1 * d2, q, G);
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
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
>   CheckSize(G);
>   CheckIsSubsetSU(d1 * d2, q, G);
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
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
>   CheckSize(G);
>   CheckIsSubsetSp(d1 * d2, q, G);
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
> end;;
gap> TestTensorProductStabilizerInSp(0, 2, 3, 3);
gap> TestTensorProductStabilizerInSp(0, 4, 3, 5);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestTensorProductStabilizerInSp(1, 2, 4, 5);
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
gap> STOP_TEST("TensorProductMatrixGroups.tst", 0);
