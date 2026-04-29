gap> START_TEST("ImprimitiveMatrixGroups.tst");
gap> oldOrbInfoLevel:=InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoOrb, 0); # silence `Giving up, Schreier tree is not shallow.` warnings

#
gap> TestImprimitivesMeetSL := function(n, q, t)
>   local G;
>   G := ImprimitivesMeetSL(n, q, t);
>   CheckIsSubsetSL(n, q, G);
>   CheckSize(G);
> end;;
gap> TestImprimitivesMeetSL(2, 3, 2);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestImprimitivesMeetSL(4, 8, 2); # FIXME: `Error, !!!`, see https://github.com/gap-packages/recog/issues/12
#@fi
gap> TestImprimitivesMeetSL(6, 5, 3);

#
gap> TestSUIsotropicImprimitives := function(n, q)
>   local G;
>   G := SUIsotropicImprimitives(n, q);
>   CheckIsSubsetSU(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSUIsotropicImprimitives(6, 2);
gap> TestSUIsotropicImprimitives(4, 3);
gap> TestSUIsotropicImprimitives(2, 5);

#
gap> TestSUNonDegenerateImprimitives := function(n, q, t)
>   local G;
>   G := SUNonDegenerateImprimitives(n, q, t);
>   CheckIsSubsetSU(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSUNonDegenerateImprimitives(6, 3, 3);
gap> TestSUNonDegenerateImprimitives(9, 2, 3);
gap> TestSUNonDegenerateImprimitives(3, 5, 3);

#
gap> TestSpIsotropicImprimitives := function(n, q)
>   local G;
>   G := SpIsotropicImprimitives(n, q);
>   CheckIsSubsetSp(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSpIsotropicImprimitives(4, 3);
gap> TestSpIsotropicImprimitives(4, 7);
gap> TestSpIsotropicImprimitives(6, 5);
gap> TestSpIsotropicImprimitives(8, 3);

# Test error handling
gap> SpIsotropicImprimitives(3, 3);
Error, <d> must be even
gap> SpIsotropicImprimitives(4, 2);
Error, <q> must be odd

#
gap> TestSpNonDegenerateImprimitives := function(n, q, t)
>   local G;
>   G := SpNonDegenerateImprimitives(n, q, t);
>   CheckIsSubsetSp(n, q, G);
>   CheckSize(G);
> end;;
gap> TestSpNonDegenerateImprimitives(4, 2, 2);
gap> TestSpNonDegenerateImprimitives(6, 5, 3);
gap> TestSpNonDegenerateImprimitives(10, 3, 5);
gap> TestSpNonDegenerateImprimitives(12, 3, 3);

# Test error handling
gap> SpNonDegenerateImprimitives(3, 3, 3);
Error, <d> must be even
gap> SpNonDegenerateImprimitives(4, 3, 3);
Error, <t> must divide <d>
gap> SpNonDegenerateImprimitives(6, 3, 2);
Error, <m> = <d> / <t> must be even

#
gap> TestOmegaNonDegenerateImprimitives := function(epsilon, n, q, epsilon_0, t)
>   local G;
>   G := OmegaNonDegenerateImprimitives(epsilon, n, q, epsilon_0, t);
>   CheckIsSubsetOmega(epsilon, n, q, G);
>   CheckSize(G);
> end;;
gap> TestOmegaNonDegenerateImprimitives(0, 7, 7, 0, 7);
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOmegaNonDegenerateImprimitives(0, 9, 9, 0, 3);
#@fi
gap> TestOmegaNonDegenerateImprimitives(0, 15, 3, 0, 3);
gap> TestOmegaNonDegenerateImprimitives(0, 15, 3, 0, 5);
gap> TestOmegaNonDegenerateImprimitives(1, 8, 8, -1, 2);
gap> TestOmegaNonDegenerateImprimitives(1, 8, 5, 1, 4);
gap> TestOmegaNonDegenerateImprimitives(1, 8, 11, 0, 8);
gap> TestOmegaNonDegenerateImprimitives(-1, 10, 4, -1, 5);
gap> TestOmegaNonDegenerateImprimitives(-1, 12, 3, -1, 3);

# Test error handling
gap> OmegaNonDegenerateImprimitives(0, 6, 7, 0, 7);
Error, <d> must be odd
gap> OmegaNonDegenerateImprimitives(1, 7, 7, 0, 7);
Error, <d> must be even
gap> OmegaNonDegenerateImprimitives(2, 7, 7, 0, 7);
Error, <epsilon> must be in [-1, 0, 1]
gap> OmegaNonDegenerateImprimitives(0, 7, 4, 0, 7);
Error, <d> must be even if <q> is even
gap> OmegaNonDegenerateImprimitives(0, 7, 3, 0, 3);
Error, <t> must be a divisor of <d>
gap> OmegaNonDegenerateImprimitives(-1, 8, 4, 1, 2);
Error, <epsilon_0> ^ t must be equal to <epsilon> if <d> / <t> is even
gap> OmegaNonDegenerateImprimitives(-1, 6, 5, 1, 2);
Error, <epsilon_0> must be 0 in case <d> / <t> is odd
gap> OmegaNonDegenerateImprimitives(1, 6, 3, 0, 2);
Error, discriminant must be square in case <d> / <t> is odd and <t> is even
gap> OmegaNonDegenerateImprimitives(1, 8, 9, 0, 8);
Error, <q> must be an odd prime in case <t> = <d>

#
gap> TestOmegaIsotropicImprimitives := function(n, q)
>   local G;
>   G := OmegaIsotropicImprimitives(n, q);
>   CheckIsSubsetOmega(1, n, q, G);
>   CheckSize(G);
> end;;
gap> TestOmegaIsotropicImprimitives(8, 8);
gap> TestOmegaIsotropicImprimitives(8, 7);
gap> TestOmegaIsotropicImprimitives(10, 4);
gap> TestOmegaIsotropicImprimitives(10, 5);

# Test error handling
gap> OmegaIsotropicImprimitives(5, 5);
Error, <d> must be even

#
gap> TestOmegaNonIsometricImprimitives := function(epsilon, n, q)
>   local G;
>   G := OmegaNonIsometricImprimitives(epsilon, n, q);
>   CheckIsSubsetOmega(epsilon, n, q, G);
>   CheckSize(G);
> end;;
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestOmegaNonIsometricImprimitives(1, 6, 7);
gap> TestOmegaNonIsometricImprimitives(-1, 6, 9); # see https://github.com/gap-packages/ClassicalMaximals/pull/111
#@fi
gap> TestOmegaNonIsometricImprimitives(1, 10, 3);
gap> TestOmegaNonIsometricImprimitives(-1, 10, 5);

# Test error handling
gap> OmegaNonIsometricImprimitives(2, 6, 3);
Error, <epsilon> must be -1 or 1
gap> OmegaNonIsometricImprimitives(1, 5, 3);
Error, <d> must be even
gap> OmegaNonIsometricImprimitives(1, 8, 3);
Error, <d> / 2 must be odd
gap> OmegaNonIsometricImprimitives(1, 6, 4);
Error, <q> must be odd
gap> OmegaNonIsometricImprimitives(1, 6, 5);
Error, discriminant must be nonsquare

#
gap> SetInfoLevel(InfoOrb, oldOrbInfoLevel);
gap> STOP_TEST("ImprimitiveMatrixGroups.tst", 0);
