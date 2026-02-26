gap> TestModularReductionOfIntegralLattice := function(LR, q, expectedOrbitNumber)
>     local special, general, normaliser, result;
>     special := ValueOption("special");
>     if special = fail then special := false; fi;
>     general := ValueOption("general");
>     if general = fail then general := false; fi;
>     normaliser := ValueOption("normaliser");
>     if normaliser = fail then normaliser := false; fi;
>     result := ModularReductionOfIntegralLattice(LR, q :
>                                                 special := special,
>                                                 general := general,
>                                                 normaliser := normaliser);
>     Assert(0, Length(result) = expectedOrbitNumber);
> end;;
gap> LR := ReadAsFunction(Filename(CM_c9lib, "sl25d2.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 11, 1);;  # 1-dimensional module discarded
gap> LR := ReadAsFunction(Filename(CM_c9lib, "2a6d4.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 11, 1);;  # new module found and appended
gap> LR := ReadAsFunction(Filename(CM_c9lib, "m11d11.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 3, 2);;  # na = 0, so perm () added

#
gap> LR := ReadAsFunction(Filename(CM_c9lib, "l27d3.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 11, 1 : general:=true);;  # "linear", general
gap> LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 13, 1);;  # "linear", stabil. automorphism
gap> LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 19, 1);;  # "linear", root computation of det
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a6d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 13, 1);;  # "linear", root computation failed, continue
gap> LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 19, 1);;  # "linear", ox > 1
gap> LR := ReadAsFunction(Filename(CM_c9lib, "4al34d8.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 17^2, 2);;  # "linear", RootsOfUPol not empty
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a6d9.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 7, 1 : general:=true);;  # "linear", v * I_d has det 1
gap> LR := ReadAsFunction(Filename(CM_c9lib, "4al34d8.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 29, 2 : general:=true);;  # "linear", if general and not got
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a6d3.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 19, 1);  # "linear", last scalar adjoined

#
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a7d21b.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 5^2, 2 : normaliser:=true);;  # "unitary", normaliser
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a7d21b.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 5^2, 2 : general:=true);;  # "unitary", general
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a6d3.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 5^2, 1);;  # "unitary", stabil. automorphism
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a6d3.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 5^2, 1);; # "unitary", try to make det of iso 1
gap> LR := ReadAsFunction(Filename(CM_c9lib, "4bl34d20.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 3^2, 2);;  # "unitary", not general and not got, continue
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a6d3.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 5^2, 1);;  # "unitary", v * I_d has det 1 and is in GU
gap> LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 11^2, 1 : normaliser:=true);;  # if normaliser and not got
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a7d21b.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 5^2, 2 : general:=true);;  # "unitary", last scalar adjoined
gap> LR := ReadAsFunction(Filename(CM_c9lib, "3a7d21b.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 5^2, 2 : normaliser:=true);;  # "unitary, last scalar adjoined

#
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a9d8.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 2, 1);;  # "else", quad:=true
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a5d4.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 7, 1);;  # "else", stabil. automorphism
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a9d8.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 2, 1);;  # "else", quad ... mat[j,i] <> Zero(GF(q)) and not got
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a5d4.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 7, 1);;  # "else", root of scal computation
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a7d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 7, 1);;  # "else", det = -1 and d odd
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a5d4.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 7, 1);;  # "else", elif not general and det <> -1
gap> LR := ReadAsFunction(Filename(CM_c9lib, "l33d12.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 11, 1);;  # "else", iso := - iso (only sometimes)
gap> LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 3, 1);;  # "else", else (dsq, iso := - iso)
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a7d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 7, 1);;  # "else", orthogonalcircle and iso not in Omega, continue
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a6d10.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 13, 1 : normaliser:=true);;  # "else", special and ox > 1, normaliser and not got
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a7d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 7, 1 : normaliser:=true);;  # "else", last scalar adjoined
gap> LR := ReadAsFunction(Filename(CM_c9lib, "a7d6.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 7, 1);;  # "else", last scalar adjoined

# TODO "else", if special and ox > 1 then ... v * I_d has det 1 ... is not covered

#
gap> LR := ReadAsFunction(Filename(CM_c9lib, "l213d12.g"))();;
gap> TestModularReductionOfIntegralLattice(LR, 43, 3);;

# Test error handling
gap> LR := ReadAsFunction(Filename(CM_c9lib, "sl25d2.g"))();;
gap> ModularReductionOfIntegralLattice(LR, 3);
Error, Constituents are not absolutely irreducible over finite field.
