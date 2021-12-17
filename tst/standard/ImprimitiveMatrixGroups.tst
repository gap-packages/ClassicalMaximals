gap> START_TEST("ImprimitiveMatrixGroups.tst");

#
gap> TestImprimitivesMeetSL := function(args)
>   local n, q, t, G;
>   n := args[1];
>   q := args[2];
>   t := args[3];
>   G := ImprimitivesMeetSL(n, q, t);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSL(n, q, G));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestImprimitivesMeetSL([2, 3, 2]);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestImprimitivesMeetSL([4, 8, 2]); # FIXME: `Error, !!!`, see https://github.com/gap-packages/recog/issues/12
#@fi
gap> TestImprimitivesMeetSL([6, 5, 3]);

#
gap> TestSUIsotropicImprimitives := function(args)
>   local n, q, G;
>   n := args[1];
>   q := args[2];
>   G := SUIsotropicImprimitives(n, q);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSU(n, q, G));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestSUIsotropicImprimitives([6, 2]);
gap> TestSUIsotropicImprimitives([4, 3]);
gap> TestSUIsotropicImprimitives([2, 5]);

#
gap> TestSUNonDegenerateImprimitives := function(args)
>   local n, q, t, G;
>   n := args[1];
>   q := args[2];
>   t := args[3];
>   G := SUNonDegenerateImprimitives(n, q, t);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSU(n, q, G));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestSUNonDegenerateImprimitives([6, 3, 3]);
gap> TestSUNonDegenerateImprimitives([9, 2, 3]);
gap> TestSUNonDegenerateImprimitives([3, 5, 3]);

#
gap> TestSpIsotropicImprimitives := function(args)
>   local n, q, G;
>   n := args[1];
>   q := args[2];
>   G := SpIsotropicImprimitives(n, q);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSp(n, q, G));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestSpIsotropicImprimitives([4, 3]);
gap> TestSpIsotropicImprimitives([4, 7]);
gap> TestSpIsotropicImprimitives([6, 5]);
gap> TestSpIsotropicImprimitives([8, 3]);

# Test error handling
gap> SpIsotropicImprimitives(3, 3);
Error, <d> must be even
gap> SpIsotropicImprimitives(4, 2);
Error, <q> must be odd

#
gap> TestSpNonDegenerateImprimitives := function(args)
>   local n, q, t, G;
>   n := args[1];
>   q := args[2];
>   t := args[3];
>   G := SpNonDegenerateImprimitives(n, q, t);
>   Assert(0, HasSize(G));
>   Assert(0, IsSubsetSp(n, q, G));
>   RECOG.TestGroup(G, false, Size(G));
> end;;
gap> TestSpNonDegenerateImprimitives([4, 2, 2]);
gap> TestSpNonDegenerateImprimitives([6, 5, 3]);
gap> TestSpNonDegenerateImprimitives([10, 3, 5]);
gap> TestSpNonDegenerateImprimitives([12, 3, 3]);

# Test error handling
gap> SpNonDegenerateImprimitives(3, 3, 3);
Error, <d> must be even
gap> SpNonDegenerateImprimitives(4, 3, 3);
Error, <t> must divide <d>
gap> SpNonDegenerateImprimitives(6, 3, 2);
Error, <m> = <d> / <t> must be even

#
gap> STOP_TEST("ImprimitiveMatrixGroups.tst", 0);
