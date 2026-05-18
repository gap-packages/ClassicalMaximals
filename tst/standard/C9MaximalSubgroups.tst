gap> START_TEST("C9MaximalSubgroups.tst");
gap> oldOrbInfoLevel:=InfoLevel(InfoOrb);;
gap> SetInfoLevel(InfoOrb, 0); # silence `Giving up, Schreier tree is not shallow.` warnings

#
gap> TestC9SubgroupsSpecialLinearGroupGeneric := function(n, q, opts...)
>     local general, result, G;
>     if Length(opts) = 0 then opts := rec(); else opts := opts[1]; fi;
>     general := IsBound(opts.general) and opts.general;  # default to false
>     result := C9SubgroupsSpecialLinearGroupGeneric(n, q, opts);
>     for G in result do
>         CheckIsSubsetSL(n, q, G);
>         if not general then
>             CheckSize(G);
>         fi;
>     od;
> end;;
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric := function(n, q, opts...)
>     local general, normaliser, result, G;
>     if Length(opts) = 0 then opts := rec(); else opts := opts[1]; fi;
>     general := IsBound(opts.general) and opts.general;  # default to false
>     normaliser := IsBound(opts.normaliser) and opts.normaliser;  # default to false
>     result := C9SubgroupsSpecialUnitaryGroupGeneric(n, q, opts);
>     for G in result do
>         if not normaliser then
>             CheckIsSubsetSU(n, q, G);
>         else
>             CheckIsSubsetSL(n, q, G);
>         fi;
>         if not general and not normaliser then
>             CheckSize(G);
>         fi;
>     od;
> end;;
gap> TestC9SubgroupsSymplecticGroupGeneric := function(n, q, opts...)
>     local normaliser, result, G;
>     if Length(opts) = 0 then opts := rec(); else opts := opts[1]; fi;
>     normaliser := IsBound(opts.normaliser) and opts.normaliser;  # default to false
>     result := C9SubgroupsSymplecticGroupGeneric(n, q, opts);
>     for G in result do
>         if not normaliser then
>             CheckIsSubsetSp(n, q, G);
>         else
>             CheckIsSubsetSL(n, q, G);
>         fi;
>         if not normaliser then
>             CheckSize(G);
>         fi;
>     od;
> end;;
gap> TestC9SubgroupsOrthogonalGroupGeneric := function(epsilon, n, q, opts...)
>     local special, general, normaliser, result, G;
>     if Length(opts) = 0 then opts := rec(); else opts := opts[1]; fi;
>     special := IsBound(opts.special) and opts.special;  # default to false
>     general := IsBound(opts.general) and opts.general;  # default to false
>     normaliser := IsBound(opts.normaliser) and opts.normaliser;  # default to false
>     result := C9SubgroupsOrthogonalGroupGeneric(epsilon, n, q, opts);
>     for G in result do
>         if not normaliser then
>             CheckIsSubsetOmega(epsilon, n, q, G);
>         else
>             CheckIsSubsetSL(n, q ,G);
>         fi;
>         if not special and not general and not normaliser then
>             CheckSize(G);
>         fi;
>     od;
> end;;
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,4, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,11, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,7^2, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(2,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,11, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,19, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(3,7^2, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,11, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7, rec(novelties:=true));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,7, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,13, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(4,2, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,3, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,5, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,31, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,7, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(5,3, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13^2, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,5, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,3, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,7, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,19, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(6,13^2, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,5, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,5, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(7,29, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,29, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,3^2, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,17^2, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,41, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,241, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(8,5, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(9,5, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(9,5, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,2, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,23, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,9, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,53, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,5, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(10,3, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,2, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,7, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,13, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(11,2, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,31, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13^2, rec(novelties:=true));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13^2, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,13, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,31, rec(all:=false));
gap> TestC9SubgroupsSpecialLinearGroupGeneric(12,49, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,5, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,13, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,29, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(3,5, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,13, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,13, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,11, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,3, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(4,3^2, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,5, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,7, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,19, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(5,29, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,17, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,23, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,7, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,17, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,2, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(6,23, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,7, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(7,83, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,11, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,19, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,59, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,71, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,31, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(8,79, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,2, rec(novelties:=true, all:=false));
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,107, rec(all:=false));  # Error, Orbit too long, increase opt.OrbitLengthLimit
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(9,2, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(10,19, rec(novelties:=true, all:=false));
#@if IsBound(CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS)
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(10,31, rec(all:=false));  # Error, Orbit too long, increase opt.OrbitLengthLimit
#@fi
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(11,5, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(11,43, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,11, rec(all:=false));
gap> TestC9SubgroupsSpecialUnitaryGroupGeneric(12,5, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(4,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(4,7, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(4,11, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(4,2^3, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,9, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,19, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,7, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,17, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,5^2, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,11, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,3^2, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(6,2^2, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(8,5, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(8,5, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(8,11, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(8,2, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(10,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(10,7, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(10,5^2, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(10,23, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(12,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(12,3^3, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(12,7, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(12,3, rec(all:=false));
gap> TestC9SubgroupsSymplecticGroupGeneric(12,2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,3,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,3,11, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,3,7^2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,4,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,4,7, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,5,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,5,11, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,5,7, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,13, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,31, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,11, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,29, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,7, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,6,13, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,13, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,19, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,11, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,17, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,29, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,6,3, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,7,3, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,7,3, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,5, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,5, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,3, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,8,2^2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,8,13, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,13, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,13, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,3^2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,9,11, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,13, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,31, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,29, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,37, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,31, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,37, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,10,3, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,11, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,19, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,2, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,13, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,19, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,10,7, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,5, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,7, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(0,11,13, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,17, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,23, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,13, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,19, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(1,12,29, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,7, rec(novelties:=true, all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,41, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,3^2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,2^2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,11^3, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,11, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,2, rec(all:=false));
gap> TestC9SubgroupsOrthogonalGroupGeneric(-1,12,7, rec(all:=false));

#
gap> SetInfoLevel(InfoOrb, oldOrbInfoLevel);
gap> STOP_TEST("C9MaximalSubgroups.tst", 0);
