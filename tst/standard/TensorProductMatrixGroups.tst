gap> START_TEST("TensorProductMatrixGroups.tst");

#
gap> TestTensorProductStabilizerInSL := function(args)
>   local d1, d2, q, G;
>   d1 := args[1];
>   d2 := args[2];
>   q := args[3];
>   G := TensorProductStabilizerInSL(d1, d2, q);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSL(d1 * d2, q, G));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestTensorProductStabilizerInSL([2, 3, 2]);
gap> TestTensorProductStabilizerInSL([2, 3, 3]);
gap> TestTensorProductStabilizerInSL([2, 3, 4]);
gap> TestTensorProductStabilizerInSL([2, 3, 5]);
gap> TestTensorProductStabilizerInSL([2, 4, 3]);
gap> TestTensorProductStabilizerInSL([3, 4, 2]);
gap> TestTensorProductStabilizerInSL([3, 4, 3]);

#
gap> TestTensorProductStabilizerInSU := function(args)
>   local d1, d2, q, G;
>   d1 := args[1];
>   d2 := args[2];
>   q := args[3];
>   G := TensorProductStabilizerInSU(d1, d2, q);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSU(d1 * d2, q, G));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q ^ 2));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestTensorProductStabilizerInSU([2, 3, 2]);
gap> TestTensorProductStabilizerInSU([2, 3, 3]);
gap> TestTensorProductStabilizerInSU([2, 3, 4]);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestTensorProductStabilizerInSU([2, 4, 3]); # FIXME: see https://github.com/gap-packages/recog/issues/302
#@fi

#
gap> TestTensorProductStabilizerInSp := function(args)
>   local epsilon, d1, d2, q, G;
>   epsilon := args[1];
>   d1 := args[2];
>   d2 := args[3];
>   q := args[4];
>   G := TensorProductStabilizerInSp(epsilon, d1, d2, q);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSp(d1 * d2, q, G));
>   Assert(0, DefaultFieldOfMatrixGroup(G) = GF(q));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestTensorProductStabilizerInSp([0, 2, 3, 3]);
gap> TestTensorProductStabilizerInSp([0, 4, 3, 5]);
gap> TestTensorProductStabilizerInSp([1, 2, 4, 5]);
gap> TestTensorProductStabilizerInSp([-1, 2, 4, 5]);

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
