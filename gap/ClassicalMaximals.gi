#
# ClassicalMaximals: Maximal subgroups of classical groups
#
# Code along the lines of [BHR13], [KL90], [HR05] and [HR10].
#
# Implementations
#

# For most classes of subgroups, we have to conjugate the subgroups we
# determined by an element C from the general group, which is not in the
# special (or quasisimple) group, in order to get representatives for all
# conjugacy classes in the special (or quasisimple) group, not only for the
# conjugacy classes in the general group (which are generally larger).
BindGlobal("ConjugatesInGeneralGroup",
function(S, C, r)
    return List([0..r - 1], i -> S ^ (C ^ i));
end);

# TODO This needs to be moved to a more suitable location.
BindGlobal("CM_c9lib",
DirectoriesPackageLibrary("ClassicalMaximals", "data/c9lattices"));

InstallGlobalFunction(ClassicalMaximalsGeneric,
function(type, n, q, classes...)
    if Length(classes) = 0 then
        classes := [1..9];
    elif Length(classes) = 1 and IsList(classes[1]) then
        classes := classes[1];
    fi;
    if not IsSubset([1..9], classes) then
        ErrorNoReturn("<classes> must be a subset of [1..9]");
    fi;

    if type = "L" then
        return MaximalSubgroupClassRepsSpecialLinearGroup(n, q, classes);
    elif type = "U" then
        return MaximalSubgroupClassRepsSpecialUnitaryGroup(n, q, classes);
    elif type = "S" then
        return MaximalSubgroupClassRepsSymplecticGroup(n, q, classes);
    elif type = "O-" then
        return MaximalSubgroupClassRepsOrthogonalGroup(-1, n, q, classes);
    elif type = "O" then
        return MaximalSubgroupClassRepsOrthogonalGroup(0, n, q, classes);
    elif type = "O+" then
        return MaximalSubgroupClassRepsOrthogonalGroup(1, n, q, classes);
    fi;
    ErrorNoReturn("Type must be in ['L', 'U', 'S', 'O-', 'O', 'O+']");
end);

# Return an element of GL(n, q) \ SL(n, q).
InstallGlobalFunction("GLMinusSL",
function(n, q)
    local F, result;
    F := GF(q);
    result := IdentityMat(n, F);
    result[1, 1] := Z(q);
    return ImmutableMatrix(F, result);
end);

BindGlobal("C1SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    return List([1..n-1], k -> SLStabilizerOfSubspace(n, q, k));
end);

BindGlobal("C2SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    local t, divisors, result;
    divisors := DivisorsInt(n);
    result := [];
    for t in divisors{[2..Length(divisors)]} do
        # not maximal or considered in class C_1 or C_8 by Proposition
        # 2.3.6 of [BHR13]
        if (n > 2 and t = n and q <= 4) or (t = n / 2 and q = 2) then
            continue;  
        fi;
        Add(result, ImprimitivesMeetSL(n, q, t));
    od;
    return result;
end);

BindGlobal("C3SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    return List(PrimeDivisors(n), s -> GammaLMeetSL(n, q, s));
end);

BindGlobal("C4SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    local divisorListOfn, result, n1, numberOfConjugates, generatorGLMinusSL,
    tensorProductSubgroup;
    
    divisorListOfn := List(DivisorsInt(n));
    Remove(divisorListOfn, 1);
    divisorListOfn := Filtered(divisorListOfn, x -> x < n / x);
    # Cf. Proposition 2.3.22
    if q = 2 and 2 in divisorListOfn then
        RemoveSet(divisorListOfn, 2);
    fi;
    result := [];
    
    generatorGLMinusSL := GLMinusSL(n, q);
    for n1 in divisorListOfn do
        tensorProductSubgroup := TensorProductStabilizerInSL(n1, QuoInt(n, n1), q);
        # Cf. Tables 3.5.A and 3.5.G in [KL90]
        numberOfConjugates := Gcd([q - 1, n1, QuoInt(n, n1)]);
        Append(result, ConjugatesInGeneralGroup(tensorProductSubgroup, 
                                               generatorGLMinusSL,
                                               numberOfConjugates));
    od;

    return result;
end);

BindGlobal("C5SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    local factorisation, p, e, generatorGLMinusSL, primeDivisorsOfe,
    degreeOfExtension, f, subfieldGroup, numberOfConjugates, result;
    
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGLMinusSL := GLMinusSL(n, q);
    primeDivisorsOfe := PrimeDivisors(e);

    result := [];
    for degreeOfExtension in primeDivisorsOfe do
        f := QuoInt(e, degreeOfExtension);
        subfieldGroup := SubfieldSL(n, p, e, f);
        # Cf. Tables 3.5.A and 3.5.G in [KL90]
        numberOfConjugates := Gcd(n, QuoInt(q - 1, p ^ f - 1));
        Append(result, ConjugatesInGeneralGroup(subfieldGroup, 
                                                generatorGLMinusSL, 
                                                numberOfConjugates));
    od;

    return result;
end);

BindGlobal("C6SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    local factorisationOfq, p, e, factorisationOfn, r, m, result,
    generatorGLMinusSL, numberOfConjugates, extraspecialNormalizerSubgroup;

    result := [];
    if not IsPrimePowerInt(n) then
        return result;
    fi;
    
    factorisationOfq := PrimePowersInt(q);
    p := factorisationOfq[1];
    e := factorisationOfq[2];
    factorisationOfn := PrimePowersInt(n);
    r := factorisationOfn[1];
    m := factorisationOfn[2];
    generatorGLMinusSL := GLMinusSL(n, q);

    # Cf. Table 4.6.B and the corresponding definition in [KL90]
    if IsOddInt(r) then
        if IsOddInt(e) and e = OrderMod(p, r) then
            extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSL(r, m, q);
            # Cf. Tables 3.5.A and 3.5.G in [KL90]
            numberOfConjugates := Gcd(n, q - 1);
            if n = 3 and ((q - 4) mod 9 = 0 or (q - 7) mod 9 = 0) then
                numberOfConjugates := 1;
            fi;
            Append(result, ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                                    generatorGLMinusSL, 
                                                    numberOfConjugates)); 
        fi;
    elif m >= 2 then
        # n = 2 ^ m >= 4
        if e = 1 and (q - 1) mod 4 = 0 then
            extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSL(2, m, q);
            # Cf. Tables 3.5.A and 3.5.G in [KL90]
            numberOfConjugates := Gcd(n, q - 1);
            if n = 4 and (q - 5) mod 8 = 0 then
                numberOfConjugates := 2;
            fi;
            Append(result, ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                                    generatorGLMinusSL, 
                                                    numberOfConjugates));
        fi;
    else
        # n = 2
        if e = 1 and (q - 1) mod 2 = 0 then
            extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSL(2, 1, q);
            if (q - 1) mod 8 = 0 or (q - 7) mod 8 = 0 then
                # Cf. Tables 3.5.A and 3.5.G in [KL90]
                numberOfConjugates := Gcd(n, q - 1);
                Append(result, ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, ExtraspecialNormalizerInSL(2, 1, q));
            fi;
        fi;
    fi;

    return result;
end);

BindGlobal("C7SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    local m, t, factorisationOfn, factorisationOfnExponents, highestPowern,
    result, divisorsHighestPowern, numberOfConjugates, tensorInducedSubgroup, 
    generatorGLMinusSL;

    result := [];
    generatorGLMinusSL := GLMinusSL(n, q);
    factorisationOfn := PrimePowersInt(n);
    # get all exponents of prime factorisation of n
    factorisationOfnExponents := factorisationOfn{Filtered([1..Length(factorisationOfn)], 
                                                  IsEvenInt)};
    # n can be written as k ^ highestPowern with k an integer and highestPowern
    # is maximal with this property
    highestPowern := Gcd(factorisationOfnExponents);
    
    divisorsHighestPowern := DivisorsInt(highestPowern);

    for t in divisorsHighestPowern{[2..Length(divisorsHighestPowern)]} do
        m := RootInt(n, t);
        if m < 3 then
            continue;
        fi;
        tensorInducedSubgroup := TensorInducedDecompositionStabilizerInSL(m, t, q);
        # Cf. Tables 3.5.A and 3.5.G in [KL90]
        numberOfConjugates := Gcd(q - 1, m ^ (t - 1));
        if m mod 4 = 2 and t = 2 and q mod 4 = 3 then
            numberOfConjugates := Gcd(q - 1, m) / 2;
        fi;
        Append(result, ConjugatesInGeneralGroup(tensorInducedSubgroup,
                                                generatorGLMinusSL, 
                                                numberOfConjugates));
    od;

    return result;
end);

BindGlobal("C8SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    local factorisation, p, e, result, generatorGLMinusSL, symplecticSubgroup,
    numberOfConjugatesSymplectic, unitarySubgroup, numberOfConjugatesUnitary,
    orthogonalSubgroup, numberOfConjugatesOrthogonal, epsilon;
    
    result := [];
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGLMinusSL := GLMinusSL(n, q);

    if IsEvenInt(n) then
        symplecticSubgroup := SymplecticNormalizerInSL(n, q);
        # Cf. Tables 3.5.A and 3.5.G in [KL90]
        numberOfConjugatesSymplectic := Gcd(q - 1, QuoInt(n, 2));
        Append(result, ConjugatesInGeneralGroup(symplecticSubgroup, 
                                                generatorGLMinusSL,
                                                numberOfConjugatesSymplectic));
    fi;

    if IsEvenInt(e) then
        unitarySubgroup := UnitaryNormalizerInSL(n, q);
        # Cf. Tables 3.5.A and 3.5.G in [KL90]
        numberOfConjugatesUnitary := Gcd(p ^ QuoInt(e, 2) - 1, n);
        Append(result, ConjugatesInGeneralGroup(unitarySubgroup,
                                                generatorGLMinusSL,
                                                numberOfConjugatesUnitary));
    fi;

    if IsOddInt(q) then
        if IsOddInt(n) then
            orthogonalSubgroup := OrthogonalNormalizerInSL(0, n, q);
            # Cf. Tables 3.5.A and 3.5.G in [KL90]
            numberOfConjugatesOrthogonal := Gcd(q - 1, n);
            Append(result, ConjugatesInGeneralGroup(orthogonalSubgroup,
                                                    generatorGLMinusSL,
                                                    numberOfConjugatesOrthogonal));
        else
            for epsilon in [1, -1] do
                orthogonalSubgroup := OrthogonalNormalizerInSL(epsilon, n, q);
                # Cf. Tables 3.5.A. and 3.5.G in [KL90]
                numberOfConjugatesOrthogonal := QuoInt(Gcd(q - 1, n), 2);
                Append(result, ConjugatesInGeneralGroup(orthogonalSubgroup,
                                                        generatorGLMinusSL,
                                                        numberOfConjugatesOrthogonal));
            od;
        fi;
    fi;

    return result;
end);

BindGlobal("C9SubgroupsSpecialLinearGroupGeneric",
function(n, q)
    local all, novelties, special, general, normaliser, result, factorisation,
          p, e, generatorGLMinusSL, LR, S, size, numberOfConjugates;
    
    all := ValueOption("all");
    if all = fail then all := true; fi;
    novelties := ValueOption("novelties");
    if novelties = fail then novelties := false; fi;
    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    result := [];
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGLMinusSL := GLMinusSL(n, q);

    if n = 2 then
        if novelties then return result; fi;
        if (e = 1 and p mod 5 in [1, 4]) or
           (e = 2 and p <> 2 and p mod 5 in [2, 3]) then
            # 2.A5
            LR := ReadAsFunction(Filename(CM_c9lib, "sl25d2.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            size := 120;
            SetSize(S[1], size);
            if all then
                numberOfConjugates := 2;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 3 then
        if novelties then return result; fi;
        if (e = 1 and p <> 2 and p mod 7 in [1, 2, 4]) then
            # L27
            LR := ReadAsFunction(Filename(CM_c9lib, "l27d3.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if general then
                size := (q - 1) * 168;
            else
                size := Gcd(q - 1, 3) * 168;
            fi;
            SetSize(S[1], size);
            if all then
                numberOfConjugates := Gcd(p - 1, 3);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 3 = 1 and p mod 5 in [1, 4]) or
           (e = 2 and p <> 3 and p mod 5 in [2, 3]) then
            # 3.A6
            LR := ReadAsFunction(Filename(CM_c9lib, "3a6d3.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if general then
                size := (q - 1) * 360;
            else
                size := 1080;
            fi;
            SetSize(S[1], size);
            if all then
                numberOfConjugates := 3;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 4 then
        if (e = 1 and p <> 2 and p mod 7 in [1, 2, 4]) then
            if novelties then
                # 2.L27
                LR := ReadAsFunction(Filename(CM_c9lib, "sl27d4.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : general := general);
                if not general then
                    size := Gcd(q - 1, 4) * 168;
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := Gcd(q - 1, 4);
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGLMinusSL,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            else
                # 2.A7
                LR := ReadAsFunction(Filename(CM_c9lib, "2a7d4.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : general := general);
                if not general then
                    size := Gcd(q - 1, 4) * 2520;
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := Gcd(q - 1, 4);
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGLMinusSL,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
        fi;
        if novelties then return result; fi;
        if (e = 1 and p mod 6 = 1) then
            # 2.U42
            LR := ReadAsFunction(Filename(CM_c9lib, "2u42d4.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 4) * 25920;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 4);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 2 then
            # A7
            LR := ReadAsFunction(Filename(CM_c9lib, "2a7d4.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := 2520;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
        fi;
    elif n = 5 then
        if (novelties and q = 3) or
           (not novelties and e = 1 and p > 3 and p mod 11 in [1, 3, 4, 5, 9]) then
            # L2_11
            LR := ReadAsFunction(Filename(CM_c9lib, "l211d5.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 5) * 660;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 5);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if novelties then return result; fi;
        if (e = 1 and p mod 6 = 1) then
            # U42
            LR := ReadAsFunction(Filename(CM_c9lib, "u42d5.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 5) * 25920;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 5);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 3 then
            # M11
            LR := ReadAsFunction(Filename(CM_c9lib, "m11d11.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := 7920;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
            if all then
                S := Group(MTX.Generators(DualGModule(
                     GModuleByMats(GeneratorsOfGroup(S[1]),
                     GF(3)))));
                if not general then
                    size := 7920;
                    SetSize(S, size);
                fi;
                Add(result, S);
            fi;
        fi;
    elif n = 6 then
        if novelties then
            if (e = 1 and p mod 24 in [7, 13]) then
                # 6.L3_4
                LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : general := general);
                if not general then
                    size := 120960;
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := 3;
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGLMinusSL,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            if (e = 1 and p mod 24 in [1, 7]) or
               (e = 2 and p mod 24 in [5, 11, 13, 19]) then
                # 6.A6
                LR := ReadAsFunction(Filename(CM_c9lib, "6a6d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : general := general);
                if not general then
                    size := 2160;
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := 6;
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGLMinusSL,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            if (e = 1 and p mod 24 in [1, 7, 13, 19]) then
                # 3.A6
                LR := ReadAsFunction(Filename(CM_c9lib, "3a6d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : general := general);
                if not general then
                    if p mod 24 in [1, 19] then
                        size := 4320;
                    else
                        size := 2160;
                    fi;
                    SetSize(S[1], size);
                fi;
                if all then
                    if p mod 24 in [1, 19] then
                        numberOfConjugates := 6;
                    else
                        numberOfConjugates := 3;
                    fi;
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGLMinusSL,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            return result;
        fi;
        if (e = 1 and p <> 3 and p mod 11 in [1, 3, 4, 5, 9]) then
            # 2.L2_11 in 2.M12 for p = 3
            LR := ReadAsFunction(Filename(CM_c9lib, "sl211d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 6) * 660;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 6);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        elif q = 3 then
            # 2.M12
            LR := ReadAsFunction(Filename(CM_c9lib, "2m12d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := 190080;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 2;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 12 in [1, 7]) then
            # 6_1.U4_3 (p mod 12 = 7) or 6_1.U4_3.2_2 (p mod 12 = 1)
            LR := ReadAsFunction(Filename(CM_c9lib, "6au43d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                if p mod 12 = 1 then
                    size := 39191040;
                else
                    size := 19595520;
                fi;
                SetSize(S[1], size);
            fi;
            if all then
                if p mod 12 = 1 then
                    numberOfConjugates := 6;
                else
                    numberOfConjugates := 3;
                fi;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 24 in [1, 19]) then
            # 6.L3_4.2_1
            LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := 241920;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 6;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 24 in [1, 7]) or
           (e = 2 and p mod 24 in [5, 11, 13, 19]) then
            # 6.A7
            LR := ReadAsFunction(Filename(CM_c9lib, "6a7d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := 15120;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all then
                numberOfConjugates := 6;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
                Append(result, ConjugatesInGeneralGroup(S[2],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if IsOddInt(q) then
            S := AlmostSimpleDefiningCharacteristic_l3qdim6(q :
                                                            general := general);
            if not general then
                size := 2 * SizeSL(3, q);
                SetSize(S, size);
            fi;
            if all then
                numberOfConjugates := 2;
                Append(result, ConjugatesInGeneralGroup(S,
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S);
            fi;
        fi;
    elif n = 7 then
        if novelties then return result; fi;
        if (e = 1 and p mod 4 = 1) then
            # U33
            LR := ReadAsFunction(Filename(CM_c9lib, "u33d7b.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 7) * 6048;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 7);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 8 then
        if novelties then return result; fi;
        if (e = 1 and p mod 20 in [1, 9]) or
           (e = 2 and p mod 20 in [3, 7, 13, 17]) then
            # 4_1.L3_4 if q mod 16 <> 1 or 4_1.L34.2_3 if q mod 16 = 1
            LR := ReadAsFunction(Filename(CM_c9lib, "4al34d8.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                if (e = 1 and p mod 80 in [9, 21, 29, 41, 61, 69]) then
                    size := Gcd(q - 1, 8) * SizePSL(3, 4);
                elif (e = 1 and p mod 80 in [1, 49]) then
                    size := 8 * SizePSL(3, 4) * 2;
                elif (e = 2 and (p mod 80 in [3, 13, 27, 37] or
                                 p mod 80 in [43, 53, 67, 77])) then
                    size := 8 * SizePSL(3, 4);
                elif (e = 2 and (p mod 80 in [7, 17, 23, 33] or
                                 p mod 80 in [73, 63, 57, 47])) then
                    size := 8 * SizePSL(3, 4) * 2;
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all then
                if q mod 16 = 1 then
                    numberOfConjugates := 8;
                else
                    numberOfConjugates := QuoInt(Gcd(q - 1, 8), 2);
                fi;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
                Append(result, ConjugatesInGeneralGroup(S[2],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if q = 5 then
            # 4_1.L3_4 once
            LR := ReadAsFunction(Filename(CM_c9lib, "4al34d8.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := 80640;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 2;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 9 then
        if novelties then return result; fi;
        if (e = 1 and p mod 19 in [1, 4, 5, 6, 7, 9, 11, 16, 17]) then
            # L2_19
            LR := ReadAsFunction(Filename(CM_c9lib, "l219d9.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 9) * 3420;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 9);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 3 = 1 and p mod 5 in [2, 3]) then
            # 3.A6.2_3
            # TODO is this subgroup really maximal?
            # see Proposition 6.2.2
            LR := ReadAsFunction(Filename(CM_c9lib, "3a6d9.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 9) * 720;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 9);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 7 then
            # 3.A7
            LR := ReadAsFunction(Filename(CM_c9lib, "3a7d15b.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            S := Filtered(S, s -> Degree(s) = 9);
            if not general then
                size := 7560;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 3;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        # (3.)L3_q^2(.3).2
        S := AlmostSimpleDefiningCharacteristic_l3q2dim9l(q :
                                                          general := general);
        if not general then
            if q mod 3 = 0 then
                size := SizePSL(3, q^2) * 2;
            elif q mod 3 = 2 then
                size := SizePSL(3, q^2) * 6;
            elif q mod 9 = 1 then
                size := SizeSL(3, q^2) * 6;
            elif q mod 9 in [4, 7] then
                size := SizeSL(3, q^2) * 6;
            fi;
            SetSize(S, size);
        fi;
        if all then
            numberOfConjugates := Gcd(q - 1, 3);
            Append(result, ConjugatesInGeneralGroup(S,
                                                    generatorGLMinusSL,
                                                    numberOfConjugates));
        else
            Add(result, S);
        fi;
    elif n = 10 then
        if novelties then
            if (e = 1 and p <> 2 and p mod 28 in [1, 2, 9, 11, 15, 23, 25]) then
                # 2.l34 (p = 11, 15, 23 mod 28) or 2.l34.2 otherwise
                LR := ReadAsFunction(Filename(CM_c9lib, "2l34d10.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : general := general);
                if not general then
                    if p mod 28 in [11, 15, 23] then
                        size := QuoInt(Gcd(q - 1, 10), 2) * 40320;
                    else
                        size := Gcd(q - 1, 10) * 40320;
                    fi;
                    SetSize(S[1], size);
                fi;
                if all then
                    if p mod 28 in [1, 9, 25] then
                        numberOfConjugates := Gcd(q - 1, 10);
                    else
                        numberOfConjugates := QuoInt(Gcd(q - 1, 10), 2);
                    fi;
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGLMinusSL,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            return result;
        fi;
        if (e = 1 and p mod 19 in [1, 4, 5, 6, 7, 9, 11, 16, 17]) then
            # SL2_19
            LR := ReadAsFunction(Filename(CM_c9lib, "sl219d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 10) * 3420;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 10);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 8 in [1, 3]) then
            # 2.M12 (p = 3 mod 8) or 2.M12.2 (p = 1 mod 8)
            LR := ReadAsFunction(Filename(CM_c9lib, "2m12d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                if p mod 8 = 3 then
                    size := Gcd(q - 1, 10) * 95040;
                else
                    size := Gcd(q - 1, 10) * 190080;
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all then
                if p mod 8 = 1 then
                    numberOfConjugates := Gcd(q - 1, 10);
                else
                    numberOfConjugates := QuoInt(Gcd(q - 1, 10), 2);
                fi;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
                Append(result, ConjugatesInGeneralGroup(S[2],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if (e = 1 and p mod 28 in [1, 2, 9, 11, 15, 23, 25]) then
            # 2.M22 (p = 11, 15, 23 mod 28) or 2.M22.2 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "2m22d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                if p mod 28 in [11, 15, 23] then
                    size := Gcd(q - 1, 10) * 443520;
                else
                    size := Gcd(q - 1, 10) * 887040;
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all then
                if p mod 28 in [1, 2, 9, 25] then
                    numberOfConjugates := Gcd(q - 1, 10);
                else
                    numberOfConjugates := QuoInt(Gcd(q - 1, 10), 2);
                fi;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
                Append(result, ConjugatesInGeneralGroup(S[2],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if p >= 5 then
            S := AlmostSimpleDefiningCharacteristic_l3qdim10(q :
                                                             general := general);
            if not general then
                size := Gcd(q - 1, 10) * SizePSL(3, q) * Gcd(q - 1, 3);
                SetSize(S, size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 10);
                Append(result, ConjugatesInGeneralGroup(S,
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S);
            fi;
        fi;
        if p >= 3 then
            S := AlmostSimpleDefiningCharacteristic_l4qdim10(q :
                                                             general := general);
            if not general then
                size := Gcd(q - 1, 10) * SizePSL(4, q) * QuoInt(Gcd(q - 1, 4), 2);
                SetSize(S, size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 5);
                Append(result, ConjugatesInGeneralGroup(S,
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S);
            fi;
        fi;
        S := AlmostSimpleDefiningCharacteristic_l5qdim10(q :
                                                         general := general);
        if not general then
            size := Gcd(q - 1, 2) * SizeSL(5, q);
            SetSize(S, size);
        fi;
        if all then
            numberOfConjugates := Gcd(q - 1, 2);
            Append(result, ConjugatesInGeneralGroup(S,
                                                    generatorGLMinusSL,
                                                    numberOfConjugates));
        else
            Add(result, S);
        fi;
    elif n = 11 then
        if novelties then
            if q = 2 then
                # L2_23
                LR := ReadAsFunction(Filename(CM_c9lib, "l223d11.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : general := general);
                size := SizePSL(2, 23);
                SetSize(S[1], size);
                Add(result, S[1]);
            fi;
            return result;
        fi;
        if (e = 1 and p mod 3 = 1) then
            # U52
            LR := ReadAsFunction(Filename(CM_c9lib, "u52d11.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 11) * SizeSU(5, 2);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 11);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 23 in [1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18] and p <> 2) then
            # L2_23
            LR := ReadAsFunction(Filename(CM_c9lib, "l223d11.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 11) * 6072;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 11);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 2 then
            # M24
            LR := ReadAsFunction(Filename(CM_c9lib, "m24d23.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := 244823040;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            Add(result, S[1]);
            Add(result, S[2]);
        fi;
    elif n = 12 then
        if novelties then
            if (e = 1 and p mod 3 = 1 and p mod 5 in [1, 4]) or
               (e = 2 and p mod 5 in [2, 3] and p > 3) then
                # 6A6
                LR := ReadAsFunction(Filename(CM_c9lib, "6a6d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : general := general);
                if not general then
                    size := Gcd(q - 1, 12) * 360;
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := Gcd(q - 1, 12);
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGLMinusSL,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            return result;
        fi;
        if (e = 1 and p mod 23 in [1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18] and p <> 2) then
            # 2.L2_23
            LR := ReadAsFunction(Filename(CM_c9lib, "sl223d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 12) * 6072;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 12);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 3 = 1) then
            # 6.Suz
            LR := ReadAsFunction(Filename(CM_c9lib, "6suzd12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : general := general);
            if not general then
                size := Gcd(q - 1, 12) * 448345497600;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q - 1, 12);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 49 then
            # 12.L3_4
            S := ReadAsFunction(Filename(CM_c9lib, "12bl34d12f49.g"))();
            if general then
                S := Group(Concatenation(GeneratorsOfGroup(S),
                                         [PrimitiveElement(GF(q))
                                          * IdentityMat(n, Integers)]));
            fi;
            if not general then
                size := 241920;
            else
                size := 967680;
            fi;
            SetSize(S, size);
            if all then
                numberOfConjugates := 12;
                Append(result, ConjugatesInGeneralGroup(S,
                                                        generatorGLMinusSL,
                                                        numberOfConjugates));
            else
                Add(result, S);
            fi;
        fi;
    fi;
    return result;
end);

InstallGlobalFunction(MaximalSubgroupClassRepsSpecialLinearGroup,
function(n, q, classes...)
    local maximalSubgroups, factorisation, p, e;

    if Length(classes) = 0 then
        classes := [1..9];
    elif Length(classes) = 1 and IsList(classes[1]) then
        classes := classes[1];
    fi;
    if not IsSubset([1..9], classes) then
        ErrorNoReturn("<classes> must be a subset of [1..9]");
    fi;

    maximalSubgroups := [];

    if (n = 2 and q <= 3) then
        Error("SL(2, 2) and SL(2, 3) are soluble");
    fi;
 
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    
    if 1 in classes then
        # Class C1 subgroups ######################################################
        # Cf. Propositions 3.1.2 (n = 2), 3.2.1 (n = 3), 3.3.1 (n = 4), 
        #                  3.4.1 (n = 5), 3.5.1 (n = 6), 3.6.1 (n = 7), 
        #                  3.7.1 (n = 8), 3.8.1 (n = 9), 3.9.1 (n = 10), 
        #                  3.10.1 (n = 11), 3.11.1 (n = 12) in [BHR13]
        Append(maximalSubgroups, C1SubgroupsSpecialLinearGroupGeneric(n, q));
    fi;

    if 2 in classes then
        # Class C2 subgroups ######################################################
        if not n in [2, 4] then
            # Cf. Propositions 3.2.2. (n = 3), 3.4.2 (n = 5), 
            #                  3.5.2, 3.5.3, 3.5.4 all (n = 6), 3.6.2 (n = 7),
            #                  3.7.2, 3.7.3, 3.7.4 (all n = 8), 3.8.2 (n = 9),
            #                  3.9.2, 3.9.3, 3.9.4 (all n = 10), 3.10.2 (n = 11),
            #                  3.11.2, 3.11.3, 3.11.4, 3.11.5, 3.11.6 (n = 12) in [BHR13]
            # The exceptions mentioned in these propositions are all general
            # exceptions and are dealt with directly in the function
            # C2SubgroupsSpecialLinearGeneric
            Append(maximalSubgroups, C2SubgroupsSpecialLinearGroupGeneric(n, q));
        elif n = 2 then
            # Cf. Lemma 3.1.3 and Theorem 6.3.10 in [BHR13]
            if not q in [5, 7, 9, 11] then
                Add(maximalSubgroups, ImprimitivesMeetSL(2, q, 2));
            fi;
        else
            # n = 4

            # Cf. Proposition 3.3.2 in [BHR13]
            if q >= 7 then
                Add(maximalSubgroups, ImprimitivesMeetSL(4, q, 4));
            fi;
            # Cf. Proposition 3.3.3 in [BHR13]
            if q > 3 then
                Add(maximalSubgroups, ImprimitivesMeetSL(4, q, 2));
            fi;
        fi;
    fi;

    if 3 in classes then
        # Class C3 subgroups ######################################################
        # Cf. Propositions 3.3.4 (n = 4), 3.4.3 (n = 5), 3.5.5 (n = 6), 
        #                  3.6.3 (n = 7), 3.7.5 (n = 8), 3.8.3 (n = 9),
        #                  3.9.5 (n = 10), 3.10.3 (n = 11), 3.11.7 (n = 12) in [BHR13]
        if not n in [2, 3] then
            Append(maximalSubgroups, C3SubgroupsSpecialLinearGroupGeneric(n, q));
        elif n = 2 then
            # Cf. Lemma 3.1.4 and Theorem 6.3.10 in [BHR13]
            if not q in [7, 9] then
                Append(maximalSubgroups, C3SubgroupsSpecialLinearGroupGeneric(2, q));
            fi;
        else 
            # n = 3

            # Cf. Proposition 3.2.3 in [BHR13]
            if q <> 4 then
                Append(maximalSubgroups, C3SubgroupsSpecialLinearGroupGeneric(3, q));
            fi;
        fi;
    fi;

    if 4 in classes then
        # Class C4 subgroups ######################################################
        # Cf. Propositions 3.5.6 (n = 6), 3.7.7 (n = 8), 3.9.6 (n = 10), 
        #                  3.11.8 (n = 12) in [BHR13]
        # For all other n, class C4 is empty.
        Append(maximalSubgroups, C4SubgroupsSpecialLinearGroupGeneric(n, q));
    fi;

    if 5 in classes then
        # Class C5 subgroups ######################################################
        # Cf. Propositions 3.2.4 (n = 3), 3.3.5 (n = 4), 3.4.3 (n = 5), 
        #                  3.5.7 (n = 6), 3.6.3 (n = 7), 3.7.8 (n = 8),
        #                  3.8.4 (n = 9), 3.9.7 (n = 10), 3.10.3 (n = 11),
        #                  3.11.9 (n = 12) in [BHR13]
        if n <> 2 then
            Append(maximalSubgroups, C5SubgroupsSpecialLinearGroupGeneric(n, q));
        else
            # n = 2

            # Cf. Lemma 3.1.5 in [BHR13]
            if  p <> 2 or not IsPrimeInt(e) then
                Append(maximalSubgroups, C5SubgroupsSpecialLinearGroupGeneric(2, q));
            fi;
        fi;
    fi;

    if 6 in classes then
        # Class C6 subgroups ######################################################
        # Cf. Lemma 3.1.6 (n = 2) and Propositions 3.2.5 (n = 3), 3.3.6 (n = 4),
        #                                          3.4.3 (n = 5), 3.6.3 (n = 7),
        #                                          3.7.9 (n = 8), 3.8.5 (n = 9), 
        #                                          3.10.3 (n = 11) in [BHR13]
        # For all other n, class C6 is empty.

        # Cf. Theorem 6.3.10 in [BHR13]
        if n <> 2 or not q mod 40 in [11, 19, 21, 29] then 
            Append(maximalSubgroups, C6SubgroupsSpecialLinearGroupGeneric(n, q));
        fi;
    fi;

    if 7 in classes then
        # Class C7 subgroups ######################################################
        # Cf. Proposition 3.8.6 (n = 9) in [BHR13]
        # For all other n, class C7 is empty.
        Append(maximalSubgroups, C7SubgroupsSpecialLinearGroupGeneric(n, q));
    fi;

    if 8 in classes then
        # Class C8 subgroups ######################################################
        # Cf. Lemma 3.1.1 (n = 2) and Propositions 3.2.6 (n = 3), 3.3.7 (n = 4),
        #                                          3.4.3 (n = 5), 3.5.8 (n = 6),
        #                                          3.6.3 (n = 7), 3.7.11 (n = 8),
        #                                          3.8.7 (n = 9), 3.9.8 (n = 10),
        #                                          3.10.3 (n = 11), 3.11.10 (n = 12) in [BHR13]
        if n <> 2 then
            Append(maximalSubgroups, C8SubgroupsSpecialLinearGroupGeneric(n, q));
        fi;
    fi;

    if 9 in classes then
        # Class C9 subgroups ######################################################
        # Cf. Theorems 4.10.12 (n = 2), 4.10.2 (n = 3), 4.10.3 (n = 4),
        #              4.10.4 (n = 5), 4.10.5 (n = 6), 4.10.6 (n = 7),
        #              4.10.7 (n = 8), 4.10.8 (n = 9), 4.10.9 (n = 10),
        #              4.10.10 (n = 11), 4.10.11 (n = 12) in [BHR13]
        # Cf. Theorems 5.11.2 (n = 6), 5.11.3 (n = 9), 5.11.4 (n = 10)
        #              in [BHR13]
        # For all other n, class S2* is empty.
        # Cf. Tables 8.2 (n = 2), 8.4 (n = 3), 8.9 (n = 4), 8.19 (n = 5),
        #            8.25 (n = 6), 8.36 (n = 7), 8.45 (n = 8), 8.55 (n = 9),
        #            8.61 (n = 10), 8.71 (n = 11), 8.77 (n = 12) in [BHR13]
        Append(maximalSubgroups, C9SubgroupsSpecialLinearGroupGeneric(n, q));
    fi;

    return maximalSubgroups;
end);

# Return an element of GU(n, q) \ SU(n, q)
InstallGlobalFunction("GUMinusSU",
function(n, q)
    local F, zeta, result, halfOfn;
    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);
    result := IdentityMat(n, F);
    result[1, 1] := zeta;
    result[n, n] := zeta ^ (-q);
    return ImmutableMatrix(F, result);
end);

BindGlobal("C1SubgroupsSpecialUnitaryGroupGeneric",
function(n, q)
    local result;
    # type P_k subgroups
    result := List([1..QuoInt(n, 2)], k -> SUStabilizerOfIsotropicSubspace(n, q, k));
    # type GU(k, q) _|_ GU(n - k, q) subgroups
    Append(result, List([1..QuoCeil(n, 2) - 1], k -> SUStabilizerOfNonDegenerateSubspace(n, q, k)));
    return result;
end);

BindGlobal("C2SubgroupsSpecialUnitaryGroupGeneric",
function(n, q)
    local divisorListOfn, result;
    
    divisorListOfn := List(DivisorsInt(n));
    Remove(divisorListOfn, 1);
    # Cf. Proposition 2.3.6 in [BHR13]
    if q = 2 and 2 in divisorListOfn then
        RemoveSet(divisorListOfn, 2);
    fi;

    # type GU(m, q) Wr Sym(t) subgroups 
    result := List(divisorListOfn, t -> SUNonDegenerateImprimitives(n, q, t));
    # type GL(n / 2, q ^ 2).2 subgroups
    if IsEvenInt(n) then
        Add(result, SUIsotropicImprimitives(n, q));
    fi;

    return result;
end);

BindGlobal("C3SubgroupsSpecialUnitaryGroupGeneric",
function(n, q)
    return List(Filtered(PrimeDivisors(n), IsOddInt), 
                s -> GammaLMeetSU(n, q, s));
end);

BindGlobal("C4SubgroupsSpecialUnitaryGroupGeneric",
function(n, q)
    local divisorListOfn, result, n1, numberOfConjugates, generatorGUMinusSU,
    tensorProductSubgroup;
    
    divisorListOfn := List(DivisorsInt(n));
    Remove(divisorListOfn, 1);
    divisorListOfn := Filtered(divisorListOfn, x -> x < n / x);
    # Cf. Proposition 2.3.22
    if q = 2 and 2 in divisorListOfn then
        RemoveSet(divisorListOfn, 2);
    fi;
    result := [];
    
    generatorGUMinusSU := GUMinusSU(n, q);
    for n1 in divisorListOfn do
        tensorProductSubgroup := TensorProductStabilizerInSU(n1, QuoInt(n, n1), q);
        # Cf. Tables 3.5.B and 3.5.G in [KL90]
        numberOfConjugates := Gcd([q + 1, n1, QuoInt(n, n1)]);
        Append(result, ConjugatesInGeneralGroup(tensorProductSubgroup, 
                                                generatorGUMinusSU,
                                                numberOfConjugates));
    od;

    return result;
end);

BindGlobal("C5SubgroupsSpecialUnitaryGroupGeneric",
function(n, q)
    local factorisation, p, e, generatorGUMinusSU, primeDivisorsOfe,
    degreeOfExtension, f, subfieldGroup, numberOfConjugates, result, epsilon;
    
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGUMinusSU := GUMinusSU(n, q);
    primeDivisorsOfe := PrimeDivisors(e);

    result := [];
    # type GU subgroups
    for degreeOfExtension in primeDivisorsOfe do
        if IsEvenInt(degreeOfExtension) then
            continue;
        fi;
        f := QuoInt(e, degreeOfExtension);
        subfieldGroup := SubfieldSL(n, p, e, f);
        # Cf. Tables 3.5.B and 3.5.G in [KL90]
        numberOfConjugates := Gcd(n, QuoInt(q + 1, p ^ f + 1));
        Append(result, ConjugatesInGeneralGroup(subfieldGroup, 
                                                generatorGUMinusSU, 
                                                numberOfConjugates));
    od;

    # type GO subgroups
    if IsOddInt(q) then
        if IsOddInt(n) then 
            subfieldGroup := OrthogonalSubfieldSU(0, n, q);
            # Cf. Tables 3.5.B and 3.5.G in [KL90]
            numberOfConjugates := Gcd(n, q + 1);
            Append(result, ConjugatesInGeneralGroup(subfieldGroup,
                                                    generatorGUMinusSU,
                                                    numberOfConjugates));
        else 
            for epsilon in [-1, 1] do
                subfieldGroup := OrthogonalSubfieldSU(epsilon, n, q);
                # Cf. Tables 3.5.B and 3.5.G in [KL90]
                numberOfConjugates := QuoInt(Gcd(q + 1, n), 2);
                Append(result, ConjugatesInGeneralGroup(subfieldGroup,
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            od;
        fi;
    fi;

    # type Sp subgroups
    if IsEvenInt(n) then
        subfieldGroup := SymplecticSubfieldSU(n, q);
        # Cf. Tables 3.5.B and 3.5.G in [KL90]
        numberOfConjugates := Gcd(QuoInt(n, 2), q + 1);
        Append(result, ConjugatesInGeneralGroup(subfieldGroup,
                                                generatorGUMinusSU,
                                                numberOfConjugates));
    fi;

    return result;
end);

BindGlobal("C6SubgroupsSpecialUnitaryGroupGeneric",
function(n, q)
    local factorisationOfq, p, e, factorisationOfn, r, m, result,
    generatorGUMinusSU, numberOfConjugates, extraspecialNormalizerSubgroup;

    result := [];
    if not IsPrimePowerInt(n) then
        return result;
    fi;
    
    factorisationOfq := PrimePowersInt(q);
    p := factorisationOfq[1];
    e := factorisationOfq[2];
    factorisationOfn := PrimePowersInt(n);
    r := factorisationOfn[1];
    m := factorisationOfn[2];
    generatorGUMinusSU := GUMinusSU(n, q);

    # Cf. Table 4.6.B and the corresponding definition in [KL90]
    if IsOddInt(r) then
        if 2 * e = OrderMod(p, r) then
            extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSU(r, m, q);
            # Cf. Tables 3.5.B and 3.5.G in [KL90]
            numberOfConjugates := Gcd(n, q + 1);
            if n = 3 and ((q - 2) mod 9 = 0 or (q - 5) mod 9 = 0) then
                numberOfConjugates := 1;
            fi;
            Append(result, ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                                    generatorGUMinusSU, 
                                                    numberOfConjugates)); 
        fi;
    elif m >= 2 then
        # n = 2 ^ m >= 4
        if e = 1 and 2 * e = OrderMod(p, 4) then
            extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSU(2, m, q);
            # Cf. Tables 3.5.B and 3.5.G in [KL90]
            numberOfConjugates := Gcd(n, q + 1);
            if n = 4 and (q - 3) mod 8 = 0 then
                numberOfConjugates := 2;
            fi;
            Append(result, ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                                    generatorGUMinusSU, 
                                                    numberOfConjugates));
        fi;
    fi;

    return result;
end);

BindGlobal("C7SubgroupsSpecialUnitaryGroupGeneric",
function(n, q)
    local m, t, factorisationOfn, factorisationOfnExponents, highestPowern,
    result, divisorsHighestPowern, numberOfConjugates, tensorInducedSubgroup, 
    generatorGUMinusSU;

    result := [];
    generatorGUMinusSU := GUMinusSU(n, q);
    factorisationOfn := PrimePowersInt(n);
    # get all exponents of prime factorisation of n
    factorisationOfnExponents := factorisationOfn{Filtered([1..Length(factorisationOfn)], 
                                                  IsEvenInt)};
    # n can be written as k ^ highestPowern with k an integer and highestPowern
    # is maximal with this property
    highestPowern := Gcd(factorisationOfnExponents);
    
    divisorsHighestPowern := DivisorsInt(highestPowern);
    for t in divisorsHighestPowern{[2..Length(divisorsHighestPowern)]} do
        m := RootInt(n, t);
        if (m = 3 and q = 2) or m < 3 then
            continue;
        fi;
        tensorInducedSubgroup := TensorInducedDecompositionStabilizerInSU(m, t, q);
        # Cf. Tables 3.5.B and 3.5.G in [KL90]
        numberOfConjugates := Gcd(q + 1, m ^ (t - 1));
        if m mod 4 = 2 and t = 2 and q mod 4 = 1 then
            numberOfConjugates := Gcd(q + 1, m) / 2;
        fi;
        Append(result, ConjugatesInGeneralGroup(tensorInducedSubgroup,
                                                generatorGUMinusSU, 
                                                numberOfConjugates));
    od;

    return result;
end);

BindGlobal("C9SubgroupsSpecialUnitaryGroupGeneric",
function(n, q)
    local all, novelties, special, general, normaliser, result, factorisation,
          p, e, generatorGUMinusSU, LR, S, size, numberOfConjugates;

    all := ValueOption("all");
    if all = fail then all := true; fi;
    novelties := ValueOption("novelties");
    if novelties = fail then novelties := false; fi;
    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    result := [];
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGUMinusSU := GUMinusSU(n, q);

    if n = 3 then
        if (novelties and q = 5) or
           (not novelties and e = 1 and p <> 5 and p mod 7 in [3, 5, 6]) then
            # L27
            LR := ReadAsFunction(Filename(CM_c9lib, "l27d3.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 3) * SizePSL(2, 7);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(p + 1, 3);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if novelties then return result; fi;
        if (e = 1 and p mod 3 = 2 and p mod 5 in [1, 4]) then
            # 3.A6
            LR := ReadAsFunction(Filename(CM_c9lib, "3a6d3.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := 1080;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 3;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 5 then
            # 3.A7
            LR := ReadAsFunction(Filename(CM_c9lib, "3a7d21b.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            S := Filtered(S, s -> Degree(s) = 3);
            if not general and not normaliser then
                size := 7560;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 3;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
            # 3.M10
            LR := ReadAsFunction(Filename(CM_c9lib, "3a6d3.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := 2160;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 3;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 4 then
        if (e = 1 and p mod 7 in [3, 5, 6]) then
            if novelties then
                if p <> 3 then
                    # 2.L27
                    LR := ReadAsFunction(Filename(CM_c9lib, "sl27d4.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q * q :
                                                           general := general,
                                                           normaliser := normaliser);
                    if not general and not normaliser then
                        size := Gcd(q + 1, 4) * SizePSL(2, 7);
                        SetSize(S[1], size);
                    fi;
                    if all then
                        numberOfConjugates := Gcd(q + 1, 4);
                        Append(result, ConjugatesInGeneralGroup(S[1],
                                                                generatorGUMinusSU,
                                                                numberOfConjugates));
                    else
                        Add(result, S[1]);
                    fi;
                fi;
            else
                # 2.A7
                LR := ReadAsFunction(Filename(CM_c9lib, "2a7d4.g"))();
                S := ModularReductionOfIntegralLattice(LR, q * q :
                                                       general := general,
                                                       normaliser := normaliser);
                if not general and not normaliser then
                    size := Gcd(q + 1, 4) * 2520;
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := Gcd(q + 1, 4);
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGUMinusSU,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
        fi;
        if novelties then return result; fi;
        if (e = 1 and p mod 6 = 5) then
            # 2.U42
            LR := ReadAsFunction(Filename(CM_c9lib, "2u42d4.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 4) * SizePSU(4, 2);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 4);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 3 then
            # 4_2.L34
            LR := ReadAsFunction(Filename(CM_c9lib, "4bl34d20.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            S := Filtered(S, s -> Degree(s) = 4);
            if not general and not normaliser then
                size := 4 * SizePSL(3, 4);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 2;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 5 then
        if novelties then return result; fi;
        if (e = 1 and p mod 11 in [2, 6, 7, 8, 10]) then
            # L2_11
            LR := ReadAsFunction(Filename(CM_c9lib, "l211d5.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 5) * SizePSL(2, 11);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 5);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 6 = 5) then
            # U42
            LR := ReadAsFunction(Filename(CM_c9lib, "u42d5.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 5) * SizePSU(4, 2);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 5);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 6 then
        if novelties then
            if (e = 1 and p mod 24 in [11, 17]) then
                # 6.L3_4
                LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q * q :
                                                       general := general,
                                                       normaliser := normaliser);
                if not general and not normaliser then
                    size := 6 * SizePSL(3, 4);
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := 3;
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGUMinusSU,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            if (e = 1 and p mod 24 in [17, 23]) then
                # 6.A6
                LR := ReadAsFunction(Filename(CM_c9lib, "6a6d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q * q :
                                                       general := general,
                                                       normaliser := normaliser);
                if not general and not normaliser then
                    size := 2160;
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := 6;
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGUMinusSU,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            if (e = 1 and p mod 24 in [5, 11, 17, 23] and p <> 5) then
                # 3.A6
                LR := ReadAsFunction(Filename(CM_c9lib, "3a6d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q * q :
                                                       general := general,
                                                       normaliser := normaliser);
                if not general and not normaliser then
                    if p mod 24 in [11, 17] then
                        size := 2160;
                    else
                        size := 4320;
                    fi;
                    SetSize(S[1], size);
                fi;
                if all then
                    if p mod 24 in [5, 23] then
                        numberOfConjugates := 6;
                    else
                        numberOfConjugates := 3;
                    fi;
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGUMinusSU,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            return result;
        fi;
        if (e = 1 and p <> 2 and p mod 11 in [2, 6, 7, 8, 10]) then
            # 2.L2_11 in 3.M22 for p = 2
            LR := ReadAsFunction(Filename(CM_c9lib, "sl211d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 6) * SizePSL(2, 11);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 6);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        elif q = 2 then
            # 3.M22
            LR := ReadAsFunction(Filename(CM_c9lib, "3m22d21.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := 1330560;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 3;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
            # 3.U4_3.2_2
            LR := ReadAsFunction(Filename(CM_c9lib, "6au43d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := 3 * SizePSU(4, 3) * 2;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 3;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 12 in [5, 11]) then
            # 6_1.U4_3 (p mod 12 = 5) or 6_1.U4_3.2_2 (p mod 12 = 11)
            LR := ReadAsFunction(Filename(CM_c9lib, "6au43d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                if p mod 12 = 5 then
                    size := 6 * SizePSU(4, 3);
                else
                    size := 6 * SizePSU(4, 3) * 2;
                fi;
                SetSize(S[1], size);
            fi;
            if all then
                if p mod 12 = 11 then
                    numberOfConjugates := 6;
                else
                    numberOfConjugates := 3;
                fi;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 24 in [5, 23]) then
            # 6.L3_4.2_1
            LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := 6 * SizePSL(3, 4) * 2;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 6;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 24 in [17, 23]) then
            # 6.A7
            LR := ReadAsFunction(Filename(CM_c9lib, "6a7d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := 15120;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all then
                numberOfConjugates := 6;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
                Append(result, ConjugatesInGeneralGroup(S[2],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if IsOddInt(q) then
            S := AlmostSimpleDefiningCharacteristic_u3qdim6(q :
                                                            general := general,
                                                            normaliser := normaliser);
            if not general and not normaliser then
                size := 2 * SizeSU(3, q);
                SetSize(S, size);
            fi;
            if all then
                numberOfConjugates := 2;
                Append(result, ConjugatesInGeneralGroup(S,
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S);
            fi;
        fi;
    elif n = 7 then
        if novelties then return result; fi;
        if (e = 1 and p mod 4 = 3 and p <> 3) then
            # U33
            LR := ReadAsFunction(Filename(CM_c9lib, "u33d7b.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 7) * SizePSU(3, 3);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 7);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 8 then
        if novelties then return result; fi;
        if (e = 1 and p mod 20 in [11, 19]) then
            # 4_1.L3_4 if q mod 16 <> -1 or 4_1.L34.2_3 if q mod 16 = -1
            LR := ReadAsFunction(Filename(CM_c9lib, "4al34d8.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                if p mod 80 in [11, 19, 39, 51, 59, 71] then
                    size := Gcd(q + 1, 8) * SizePSL(3, 4);
                else
                    size := 8 * SizePSL(3, 4) * 2;
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all then
                if q mod 16 = 15 then
                    numberOfConjugates := 8;
                else
                    numberOfConjugates := QuoInt(Gcd(q + 1, 8), 2);
                fi;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
                Append(result, ConjugatesInGeneralGroup(S[2],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
    elif n = 9 then
        if novelties then
            if q = 2 then
                # L2_19
                LR := ReadAsFunction(Filename(CM_c9lib, "l219d9.g"))();
                S := ModularReductionOfIntegralLattice(LR, q * q :
                                                       general := general,
                                                       normaliser := normaliser);
                if not general and not normaliser then
                    size := 3 * SizePSL(2, 19);
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := Gcd(q + 1, 9);
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGUMinusSU,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            return result;
        fi;
        if (e = 1 and p mod 19 in [2, 3, 8, 10, 12, 13, 14, 15, 18] and p <> 2) then
            # L2_19
            LR := ReadAsFunction(Filename(CM_c9lib, "l219d9.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 9) * SizePSL(2, 19);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 9);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 3 = 2 and p mod 5 in [2, 3] and p > 2) then
            # 3.A6.2_3
            # TODO is this subgroup really maximal?
            # see Proposition 6.2.2
            LR := ReadAsFunction(Filename(CM_c9lib, "3a6d9.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 9) * 720;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 9);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 2 then
            # 3J3
            S := ReadAsFunction(Filename(CM_c9lib, "3j3d9f4.g"))();
            if normaliser then
                S := Group(Concatenation(GeneratorsOfGroup(S),
                                         [PrimitiveElement(GF(4))
                                          * IdentityMat(n, Integers)]));
            fi;
            if not general and not normaliser then
                size := 150698880;
                SetSize(S, size);
            fi;
            if all then
                numberOfConjugates := 3;
                Append(result, ConjugatesInGeneralGroup(S,
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S);
            fi;
        fi;
        # (3.)L3_q^2(.3).2
        S := AlmostSimpleDefiningCharacteristic_l3q2dim9u(q :
                                                          general := general,
                                                          normaliser := normaliser);
        if not general and not normaliser then
            if q mod 3 = 0 then
                size := SizePSL(3, q^2) * 2;
            elif q mod 3 = 1 then
                size := SizePSL(3, q^2) * 6;
            elif q mod 9 = 8 then
                size := SizeSL(3, q^2) * 2;
            elif q mod 9 in [2, 5] then
                size := SizeSL(3, q^2) * 6;
            fi;
            SetSize(S, size);
        fi;
        if all then
            numberOfConjugates := Gcd(q + 1, 3);
            Append(result, ConjugatesInGeneralGroup(S,
                                                    generatorGUMinusSU,
                                                    numberOfConjugates));
        else
            Add(result, S);
        fi;
    elif n = 10 then
        if novelties then
            if (e = 1 and p mod 28 in [3, 5, 13, 17, 19, 27] and p <> 3) then
                # 2.L34 (p = 5, 13, 17 mod 28) or 2.L34.2 otherwise
                LR := ReadAsFunction(Filename(CM_c9lib, "2l34d10.g"))();
                S := ModularReductionOfIntegralLattice(LR, q * q :
                                                       general := general,
                                                       normaliser := normaliser);
                if not general and not normaliser then
                    if p mod 28 in [5, 13, 17] then
                        size := Gcd(q + 1, 10) * SizePSL(3, 4);
                    else
                        size := Gcd(q + 1, 10) * SizePSL(3, 4) * 2;
                    fi;
                    SetSize(S[1], size);
                fi;
                if all then
                    if p mod 28 in [3, 19, 27] then
                        numberOfConjugates := Gcd(q + 1, 10);
                    else
                        numberOfConjugates := QuoInt(Gcd(q + 1, 10), 2);
                    fi;
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGUMinusSU,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            return result;
        fi;
        if (e = 1 and p mod 19 in [2, 3, 8, 10, 12, 13, 14, 15, 18] and p <> 2) then
            # SL2_19
            LR := ReadAsFunction(Filename(CM_c9lib, "sl219d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 10) * SizePSL(2, 19);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 10);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 8 in [5, 7]) then
            # 2.M12 (p = 5 mod 8) or 2.M12.2 (p = 7 mod 8)
            LR := ReadAsFunction(Filename(CM_c9lib, "2m12d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                if p mod 8 = 5 then
                    size := Gcd(q + 1, 10) * 95040;
                else
                    size := Gcd(q + 1, 10) * 95040 * 2;
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all then
                if p mod 8 = 7 then
                    numberOfConjugates := Gcd(q + 1, 10);
                else
                    numberOfConjugates := QuoInt(Gcd(q + 1, 10), 2);
                fi;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
                Append(result, ConjugatesInGeneralGroup(S[2],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if (e = 1 and p mod 28 in [3, 5, 13, 17, 19, 27]) then
            # 2.M22 (p = 5, 13, 17 mod 28) or 2.M22.2 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "2m22d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                if p mod 28 in [5, 13, 17] then
                    size := 2 * 443520;
                else
                    size := 2 * 443520 * 2;
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all then
                if p mod 28 in [3, 19, 27] then
                    numberOfConjugates := Gcd(q + 1, 10);
                else
                    numberOfConjugates := QuoInt(Gcd(q + 1, 10), 2);
                fi;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
                Append(result, ConjugatesInGeneralGroup(S[2],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if p >= 5 then
            S := AlmostSimpleDefiningCharacteristic_u3qdim10(q :
                                                             general := general,
                                                             normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 10) * SizePSU(3, q) * Gcd(q + 1, 3);
                SetSize(S, size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 10);
                Append(result, ConjugatesInGeneralGroup(S,
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S);
            fi;
        fi;
        if p >= 3 then
            S := AlmostSimpleDefiningCharacteristic_u4qdim10(q :
                                                             general := general,
                                                             normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 10) * SizePSU(4, q) * QuoInt(Gcd(q + 1, 4), 2);
                SetSize(S, size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 5);
                Append(result, ConjugatesInGeneralGroup(S,
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S);
            fi;
        fi;
        S := AlmostSimpleDefiningCharacteristic_u5qdim10(q :
                                                         general := general,
                                                         normaliser := normaliser);
        if not general and not normaliser then
            size := Gcd(q + 1, 10) * SizeSU(5, q);
            SetSize(S, size);
        fi;
        if all then
            numberOfConjugates := Gcd(q + 1, 2);
            Append(result, ConjugatesInGeneralGroup(S,
                                                    generatorGUMinusSU,
                                                    numberOfConjugates));
        else
            Add(result, S);
        fi;
    elif n = 11 then
        if novelties then return result; fi;
        if (e = 1 and p mod 3 = 2 and p <> 2) then
            # U52
            LR := ReadAsFunction(Filename(CM_c9lib, "u52d11.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 11) * SizePSU(5, 2);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 11);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 23 in [5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22]) then
            # L2_23
            LR := ReadAsFunction(Filename(CM_c9lib, "l223d11.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 11) * SizePSL(2, 23);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 11);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 12 then
        if novelties then
            if (e = 1 and p mod 3 = 2 and p mod 5 in [1, 4]) then
                # 6A6
                LR := ReadAsFunction(Filename(CM_c9lib, "6a6d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q * q :
                                                       general := general,
                                                       normaliser := normaliser);
                if not general and not normaliser then
                    size := Gcd(q + 1, 12) * 360;
                    SetSize(S[1], size);
                fi;
                if all then
                    numberOfConjugates := Gcd(q + 1, 12);
                    Append(result, ConjugatesInGeneralGroup(S[1],
                                                            generatorGUMinusSU,
                                                            numberOfConjugates));
                else
                    Add(result, S[1]);
                fi;
            fi;
            return result;
        fi;
        if (e = 1 and p mod 23 in [5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22]) then
            # 2.L2_23
            LR := ReadAsFunction(Filename(CM_c9lib, "sl223d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                size := Gcd(q + 1, 12) * SizePSL(2, 23);
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 12);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 3 = 2) then
            # 6.Suz (or 3.Suz if p = 2)
            LR := ReadAsFunction(Filename(CM_c9lib, "6suzd12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            if not general and not normaliser then
                if p = 2 then
                    size := 3 * 448345497600;
                else
                    size := Gcd(q + 1, 12) * 448345497600;
                fi;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := Gcd(q + 1, 12);
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 5 then
            # 6A7
            # TODO is this subgroup really maximal?
            # see Proposition 6.3.1 (iii)
            LR := ReadAsFunction(Filename(CM_c9lib, "6a7d24.g"))();
            S := ModularReductionOfIntegralLattice(LR, q * q :
                                                   general := general,
                                                   normaliser := normaliser);
            S := Filtered(S, s -> Degree(s) = 12);
            if not general and not normaliser then
                size := 15120;
                SetSize(S[1], size);
            fi;
            if all then
                numberOfConjugates := 6;
                Append(result, ConjugatesInGeneralGroup(S[1],
                                                        generatorGUMinusSU,
                                                        numberOfConjugates));
            else
                Add(result, S[1]);
            fi;
        fi;
    fi;
    return result;
end);

InstallGlobalFunction(MaximalSubgroupClassRepsSpecialUnitaryGroup,
function(n, q, classes...)
    local maximalSubgroups, subfieldGroup, numberOfConjugates,
    generatorGUMinusSU;

    if Length(classes) = 0 then
        classes := [1..9];
    elif Length(classes) = 1 and IsList(classes[1]) then
        classes := classes[1];
    fi;
    if not IsSubset([1..9], classes) then
        ErrorNoReturn("<classes> must be a subset of [1..9]");
    fi;


    if n = 2 then
        Error("We assume <n> to be greater or equal to 3 in case 'U' since",
              "SU(2, q) and SL(2, q) are isomorphic.");
    fi;
    if (n = 3 and q = 2) then
        Error("PSU(3, 2) is soluble");
    fi;

    generatorGUMinusSU := GUMinusSU(n, q);

    maximalSubgroups := [];

    if 1 in classes then
        # Class C1 subgroups ######################################################
        # Cf. Propositions 3.2.1 (n = 3), 3.3.1 (n = 4), 3.4.1 (n = 5), 
        #                  3.5.1 (n = 6), 3.6.1 (n = 7), 3.7.1 (n = 8), 
        #                  3.8.1 (n = 9), 3.9.1 (n = 10), 3.10.1 (n = 11), 
        #                  3.11.1 (n = 12) in [BHR13]
        Append(maximalSubgroups, C1SubgroupsSpecialUnitaryGroupGeneric(n, q));
    fi;

    if 2 in classes then
        # Class C2 subgroups ######################################################
        # Cf. Propositions 3.2.2 (n = 3), 3.3.2, 3.3.3 (all n = 4), 
        #                  3.4.2 (n = 5), 3.5.2, 3.5.3, 3.5.4 (all n = 6),
        #                  3.6.2 (n = 7), 3.7.2, 3.7.3, 3.7.4 (all n = 8),
        #                  3.8.2 (n = 9), 3.9.2, 3.9.3, 3.9.4, 3.9.5 (all n = 10),
        #                  3.10.2 (n = 11), 3.11.2, 3.11.3, 3.11.4, 3.11.5,
        #                  3.11.6 (all n = 12) in [BHR13]
        if not (n = 3 and q = 5) and not (n = 4 and q <= 3) and not (n = 6 and q = 2) then
            Append(maximalSubgroups, C2SubgroupsSpecialUnitaryGroupGeneric(n, q));
        # There are no maximal C2 subgroups for n = 3 and q = 5, cf. Theorem
        # 6.3.10 in [BHR13].
        elif n = 4 and q <= 3 then
            if q = 3 then
                Add(maximalSubgroups, SUNonDegenerateImprimitives(n, q, 2));
            else
                # q = 2
                Add(maximalSubgroups, SUNonDegenerateImprimitives(n, q, 4));
            fi;
        elif n = 6 and q = 2 then
            # Cf. Theorem 6.3.10 in [BHR13]
            Add(maximalSubgroups, SUNonDegenerateImprimitives(n, q, 2));
            Add(maximalSubgroups, SUIsotropicImprimitives(n, q));
        fi;
    fi;

    if 3 in classes then
        # Class C3 subgroups ######################################################
        # Cf. Propositions 3.2.3 (n = 3), 3.3.4 (n = 4), 3.4.3 (n = 5), 
        #                  3.5.5 (n = 6), 3.6.3 (n = 7), 3.7.5 (n = 8), 
        #                  3.8.3 (n = 9), 3.9.5 (n = 10), 3.10.3 (n = 11), 
        #                  3.11.7 (n = 12) in [BHR13]
        if not (n = 6 and q = 2) and not (n = 3 and q = 5)
                                 and not (n = 3 and q = 3)
                                 and not (n = 5 and q = 2) then
            Append(maximalSubgroups, C3SubgroupsSpecialUnitaryGroupGeneric(n, q));
        fi;
        # There are no maximal C3 subgroups in the cases excluded above, cf.
        # Proposition 3.5.5 and Theorem 6.3.10 in [BHR13]
    fi;

    if 4 in classes then
        # Class C4 subgroups ######################################################
        # Cf. Propositions 3.5.6 (n = 6), 3.7.7 (n = 8), 3.9.6 (n = 10), 
        #                  3.11.8 (n = 12) in [BHR13]
        Append(maximalSubgroups, C4SubgroupsSpecialUnitaryGroupGeneric(n, q));
    fi;

    if 5 in classes then
        # Class C5 subgroups ######################################################
        # Cf. Propositions 3.2.4 (n = 3), 3.3.5 (n = 4), 3.4.3 (n = 5), 
        #                  3.5.7 (n = 6), 3.6.3 (n = 7), 3.7.8 (n = 8),
        #                  3.8.4 (n = 9), 3.9.7 (n = 10), 3.10.3 (n = 11),
        #                  3.11.9 (n = 12) in [BHR13]
        if not (n = 3 and q = 3) and not (n = 3 and q = 5) and not (n = 4 and q = 3) then
            Append(maximalSubgroups, C5SubgroupsSpecialUnitaryGroupGeneric(n, q));
        # There are no maximal C5 subgroups for n = 3 and q = 3 or n = 3 and q = 5, 
        # cf. Proposition 3.2.4 and Theorem 6.3.10 in [BHR13]
        elif n = 4 and q = 3 then
            # type Sp
            subfieldGroup := SymplecticSubfieldSU(n, q);
            # Cf. Tables 3.5.B and 3.5.G in [KL90]
            numberOfConjugates := 2;
            Append(maximalSubgroups, ConjugatesInGeneralGroup(subfieldGroup,
                                                              generatorGUMinusSU,
                                                              numberOfConjugates));
            # type GO-
            subfieldGroup := OrthogonalSubfieldSU(-1, n, q);
            # Cf. Tables 3.5.B and 3.5.G in [KL90]
            numberOfConjugates := 2;
            Append(maximalSubgroups, ConjugatesInGeneralGroup(subfieldGroup,
                                                              generatorGUMinusSU,
                                                              numberOfConjugates));
        fi;
    fi;

    if 6 in classes then
        # Class C6 subgroups ######################################################
        # Cf. Lemma 3.1.6 (n = 2) and Propositions 3.2.5 (n = 3), 3.3.6 (n = 4),
        #                                          3.4.3 (n = 5), 3.6.3 (n = 7),
        #                                          3.7.9 (n = 8), 3.8.5 (n = 9), 
        #                                          3.10.3 (n = 11) in [BHR13]
        # For all other n, class C6 is empty.

        # Cf. Theorem 6.3.10 in [BHR13]
        if not (n = 3 and q = 5) then
            Append(maximalSubgroups, C6SubgroupsSpecialUnitaryGroupGeneric(n, q));
        fi;
    fi;

    if 7 in classes then
        # Class C7 subgroups ######################################################
        # Cf. Proposition 3.8.6 (n = 9) in [BHR13]
        # For all other n, class C7 is empty.
        Append(maximalSubgroups, C7SubgroupsSpecialUnitaryGroupGeneric(n, q));
    fi;

    if 9 in classes then
        # Class C9 subgroups ######################################################
        # Cf. Theorems 4.10.2 (n = 3), 4.10.3 (n = 4), 4.10.4 (n = 5),
        #              4.10.5 (n = 6), 4.10.6 (n = 7), 4.10.7 (n = 8),
        #              4.10.8 (n = 9), 4.10.9 (n = 10), 4.10.10 (n = 11),
        #              4.10.11 (n = 12) in [BHR13]
        # Cf. Theorems 5.11.2 (n = 6), 5.11.3 (n = 9), 5.11.4 (n = 10)
        #              in [BHR13]
        # For all other n, class S2* is empty.
        # Cf. Tables 8.6 (n = 3), 8.11 (n = 4), 8.21 (n = 5), 8.27 (n = 6),
        #            8.38 (n = 7), 8.47 (n = 8), 8.57 (n = 9), 8.63 (n = 10),
        #            8.73 (n = 11), 8.79 (n = 12) in [BHR13]
        Append(maximalSubgroups, C9SubgroupsSpecialUnitaryGroupGeneric(n, q));
    fi;

    return maximalSubgroups;
end);

# Return an element of the normalizer of Sp(n, q) in GL(n, q) that is not
# already contained in Sp(n, q), i.e. which preserves the symplectic form
# modulo a scalar
InstallGlobalFunction("NormSpMinusSp",
function(n, q)
    local F, zeta, result, halfOfn;
    
    if IsOddInt(n) then
        ErrorNoReturn("<n> must be even");
    fi;

    F := GF(q);
    zeta := PrimitiveElement(F);
    halfOfn := QuoInt(n, 2);
    result := DiagonalMat(Concatenation(List([1..halfOfn], i -> zeta),
                                        List([1..halfOfn], i -> zeta ^ 0)));
    return ImmutableMatrix(F, result);
end);

BindGlobal("C1SubgroupsSymplecticGroupGeneric",
function(n, q)
    local result;
    # type P_k subgroups
    result := List([1..QuoInt(n, 2)], k -> SpStabilizerOfIsotropicSubspace(n, q, k));
    # type Sp(2 * k, q) _|_ Sp(n - 2 * k, q) subgroups
    Append(result, List([1..QuoInt(n - 2, 4)], k -> SpStabilizerOfNonDegenerateSubspace(n, q, k)));
    return result;
end);

BindGlobal("C2SubgroupsSymplecticGroupGeneric",
function(n, q)
    local result, divisorListOfn, t;
    
    result := [];

    divisorListOfn := List(DivisorsInt(n));
    Remove(divisorListOfn, 1);

    # Cf. Proposition 2.3.6 in [BHR13]
    if q = 2 then
        RemoveSet(divisorListOfn, QuoInt(n, 2));
    fi;

    # type Sp(m, q) \wr Sym(t) subgroups
    for t in divisorListOfn do
        if IsEvenInt(QuoInt(n, t)) then
            Add(result, SpNonDegenerateImprimitives(n, q, t));
        fi;
    od;

    # type GL(n / 2, q).2 subgroups
    if IsOddInt(q) then
        Add(result, SpIsotropicImprimitives(n, q));
    fi;

    return result;
end);

BindGlobal("C3SubgroupsSymplecticGroupGeneric",
function(n, q)
    local primeDivisorsOfn, s, result;

    primeDivisorsOfn := PrimeDivisors(n);
    result := [];

    # symplectic type subgroups
    for s in primeDivisorsOfn do
        if IsEvenInt(n / s) then
            Add(result, SymplecticSemilinearSp(n, q, s));
        fi;
    od;

    # unitary type subgroups
    if IsEvenInt(n)  and IsOddInt(q) then
        Add(result, UnitarySemilinearSp(n, q));
    fi;

    return result;
end);

BindGlobal("C4SubgroupsSymplecticGroupGeneric",
function(n, q)
    local result, l, halfOfEvenFactorsOfn, n_1, n_2;

    if IsEvenInt(q) then
        return [];
    fi;

    result := [];

    # Instead of computing all the factors of n and
    # then only using the even ones, we factor n / 2
    # and multiply these factors by 2 when we use them.
    l := QuoInt(n, 2);
    halfOfEvenFactorsOfn := List(DivisorsInt(l));

    # This ensures n_2 >= 3
    RemoveSet(halfOfEvenFactorsOfn, l);
    RemoveSet(halfOfEvenFactorsOfn, l / 2);

    for n_1 in 2 * halfOfEvenFactorsOfn do
        n_2 := QuoInt(n, n_1);
        if IsOddInt(n_2) then
            Add(result, TensorProductStabilizerInSp(0, n_1, n_2, q));
        else
            Add(result, TensorProductStabilizerInSp(1, n_1, n_2, q));
            Add(result, TensorProductStabilizerInSp(-1, n_1, n_2, q));
        fi;
    od;
    
    return result;
end);

BindGlobal("C5SubgroupsSymplecticGroupGeneric",
function(n, q)
    local factorisation, p, e, result, generatorNormSpMinusSp, r, G, numberOfConjugates;
    
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];

    result := [];
    generatorNormSpMinusSp := NormSpMinusSp(n, q);

    # For each prime divisor of e, there is exactly one of these subgroups
    # up to conjugation in CSp, so this loop is sufficient.
    for r in PrimeDivisors(e) do
        G := SubfieldSp(n, p, e, QuoInt(e, r));

        # Cf. Proposition 4.5.4 (i) in [KL90] for the number of conjugates
        numberOfConjugates := Gcd(2, q - 1, r);
        Append(result, ConjugatesInGeneralGroup(G, generatorNormSpMinusSp, numberOfConjugates));
    od;

    return result;
end);

BindGlobal("C6SubgroupsSymplecticGroupGeneric",
function(n, q)
    local factorisationOfq, p, e, factorisationOfn, r, m, result,
    generatorNormSpMinusSp, numberOfConjugates, extraspecialNormalizerSubgroup;

    if IsEvenInt(q) then
        return [];
    fi;

    if not IsPrimePowerInt(n) then
        return [];
    fi;

    result := [];
    
    factorisationOfq := PrimePowersInt(q);
    p := factorisationOfq[1];
    e := factorisationOfq[2];
    factorisationOfn := PrimePowersInt(n);
    r := factorisationOfn[1];
    m := factorisationOfn[2];
    generatorNormSpMinusSp := NormSpMinusSp(n, q);

    # Cf. Table 4.6.B and the corresponding definition in [KL90]
    if r = 2 and e = 1 then
        extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSp(m, q);
        # Cf. Tables 3.5.C and 3.5.G in [KL90]
        if (q - 1) mod 8 = 0  or (q - 7) mod 8 = 0 then
            numberOfConjugates := 2;
        else
            numberOfConjugates := 1;
        fi;
        result := ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                           generatorNormSpMinusSp,
                                           numberOfConjugates);
    fi;

    return result;
end);

BindGlobal("C7SubgroupsSymplecticGroupGeneric",
function(n, q)
    local primeDivs, listOfts;

    if IsEvenInt(q) then
        return [];
    fi;

    primeDivs := PrimePowersInt(n);
    if Length(primeDivs) <> 2 then
        return [];
    fi;

    listOfts := Filtered(DivisorsInt(primeDivs[2]), IsOddInt);
    RemoveSet(listOfts, 1);

    # This way we avoid (m, q) = (2, 3) according to Table 2.10 in [BHR13]
    if q = 3 then
        RemoveSet(listOfts, primeDivs[2]);
    fi;

    return List(listOfts, t -> TensorInducedDecompositionStabilizerInSp(primeDivs[1] ^ QuoInt(primeDivs[2], t), t, q));
end);

BindGlobal("C8SubgroupsSymplecticGroupGeneric",
function(n, q)
    return [OrthogonalInSp(1, n, q), OrthogonalInSp(-1, n, q)];
end);

BindGlobal("C9SubgroupsSymplecticGroupGeneric",
function(n, q)
    local all, novelties, special, general, normaliser, result, factorisation,
          p, e, generatorNormSpMinusSp, S, size, LR, M, C, A;
    all := ValueOption("all");
    if all = fail then all := true; fi;
    novelties := ValueOption("novelties");
    if novelties = fail then novelties := false; fi;
    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    result := [];
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorNormSpMinusSp := NormSpMinusSp(n, q);

    if n = 4 then
        if novelties then
            if q = 7 then
                # 2.L2q
                S := AlmostSimpleDefiningCharacteristic_SymplecticSL2(4, q :
                                                                      normaliser := normaliser);
                if not normaliser then
                    size := SizeSL(2, 7);
                    SetSize(S, size);
                fi;
                Add(result, S);
            fi;
            return result;
        fi;
        if (e = 1 and p <> 7 and p mod 12 in [1, 5, 7, 11]) then
            # 2.A6 (p mod 12 in [5, 7]), 2.S6 (p mod 12 in [1, 11])
            LR := ReadAsFunction(Filename(CM_c9lib, "2a6d4.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 12 in [5, 7] then
                    size := 720;
                else
                    size := 1440;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 12 in [1, 11] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 7 then
            # 2.A7
            LR := ReadAsFunction(Filename(CM_c9lib, "2a7d4.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                size := 5040;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
        fi;
        if p >= 5 and q > 7 then
            # 2.L2q
            S := AlmostSimpleDefiningCharacteristic_SymplecticSL2(4, q :
                                                                  normaliser := normaliser);
            if not normaliser then
                size := SizeSL(2, q);
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
        if p = 2 and IsOddInt(e) and e > 1 then
            # Szq
            if normaliser then
                Add(result, Group(Concatenation(GeneratorsOfGroup(Sz(q)),
                                                [PrimitiveElement(GF(q))
                                                 * IdentityMat(n, Integers)])));
            else
                Add(result, ConjugateToStandardForm(Sz(q), "S", GF(q)));
            fi;
        fi;
    elif n = 6 then
        if novelties then
            if (e = 1 and p mod 8 in [3, 5] and p mod 5 in [1, 4]) then
                # 2.A5
                LR := ReadAsFunction(Filename(CM_c9lib, "sl25d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
                if not normaliser then
                    size := 120;
                    SetSize(S[1], size);
                fi;
                Add(result, S[1]);
            fi;
            if q = 9 then
                # 2.L_2(7)
                LR := ReadAsFunction(Filename(CM_c9lib, "sl27d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
                if not normaliser then
                    size := 2 * SizePSL(2, 7);
                    SetSize(S[1], size);
                fi;
                if all then
                    Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
                else
                    Add(result, S[1]);
                fi;
            fi;
            if (e = 1 and p mod 60 in [19, 29, 31, 41]) then
                # 2 x U_3(3)
                LR := ReadAsFunction(Filename(CM_c9lib, "u33d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
                if not normaliser then
                    size := 2 * SizePSU(3, 3);
                    SetSize(S[1], size);
                fi;
                Add(result, S[1]);
            fi;
            return result;
        fi;
        if e = 1 and (p mod 8 in [1, 7] or
                      (p mod 8 in [3, 5] and p mod 5 in [2, 3])) then
            # 2.S5 (p mod 8 in [1, 7]) or 2.A5 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "sl25d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 8 in [1, 7] then
                    size := 240;
                else
                    size := 120;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 8 in [1, 7] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 16 in [1, 15]) or
           (e = 1 and p mod 16 in [7, 9] and p <> 7) or
           (e = 2 and p mod 16 in [3, 5, 11, 13] and p <> 3) then
            # 2.L2_7.2 (e = 1 and p mod 16 in [1, 15]) or 2.L2_7 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "sl27d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if (e = 1 and p mod 16 in [1, 15]) then
                    size := 2 * SizePSL(2, 7) * 2;
                else
                    size := 2 * SizePSL(2, 7);
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all and p mod 16 in [1, 15] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp,
                                S[2], S[2] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if (e = 1 and p mod 13 in [1, 3, 4, 9, 10, 12]) or
           (e = 2 and p mod 13 in [2, 5, 6, 7, 8, 11] and p <> 2) then
            # 2.L2_13
            LR := ReadAsFunction(Filename(CM_c9lib, "sl213d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                size := 2 * SizePSL(2, 13);
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1) and
           (p mod 12 in [1, 11] or (p mod 12 in [5, 7] and p mod 5 in [2, 3])) then
            # U33.2 (p mod 12 in [1, 11]) or U33 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "u33d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 12 in [1, 11] then
                    size := 2 * SizePSU(3, 3) * 2;
                else
                    size := 2 * SizePSU(3, 3);
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 12 in [1, 11] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 5 in [0, 1, 4]) or
           (e = 2 and p mod 5 in [2, 3] and p <> 2) then
            # 2.J2
            LR := ReadAsFunction(Filename(CM_c9lib, "2j2d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                size := 1209600;
                SetSize(S[1], size);
            fi;
            if all and p <> 5 then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 9 then
            # 2.A7
            S := ReadAsFunction(Filename(CM_c9lib, "2a7d6f9.g"))();
            ConjugateToStandardForm(S, "S", GF(q));
            size := 5040;
            SetSize(S, size);
            Append(result, [S, S ^ generatorNormSpMinusSp]);
        fi;
        if p >= 7 then
            # 2.L2q
            S := AlmostSimpleDefiningCharacteristic_SymplecticSL2(6, q :
                                                                  normaliser := normaliser);
            if not normaliser then
                size := 2 * SizePSL(2, q);
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
        if p = 2 then
            M := GModuleByMats(GeneratorsOfGroup(ChevalleyG(q)), GF(q));
            C := List(MTX.CollectedFactors(M), c -> c[1]);
            A := Group(MTX.Generators(First(C, c -> MTX.Dimension(c) = 6)));
            A := ConjugateToStandardForm(A, "S", GF(q));
            if normaliser then
                A := Group(Concatenation(GeneratorsOfGroup(A),
                                         [PrimitiveElement(GF(q))
                                          * IdentityMat(n, Integers)]));
            fi;
            if not normaliser then
                size := Size(ChevalleyG(q));
                SetSize(A, size);
            fi;
            Add(result, A);
        fi;
    elif n = 8 then
        if novelties then return result; fi;
        if (e = 1 and p mod 12 in [1, 5, 7, 11] and p <> 7) then
            # 2.L27 if p mod 12 in [5, 7], 2.L27.2 if p mod 12 in [1, 11]
            LR := ReadAsFunction(Filename(CM_c9lib, "sl27d8.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 12 in [5, 7] then
                    size := 2 * SizePSL(2, 7);
                else
                    size := 2 * SizePSL(2, 7) * 2;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 12 in [1, 11] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 20 in [1, 9, 11, 19]) or
           (e = 2 and p mod 5 in [2, 3] and p <> 2 and p <> 3) then
            # 2.A6.2_2 if p mod 20 in [1, 19], 2.A6 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "2a6d8.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 20 in [1, 19] then
                    size := 1440;
                else
                    size := 720;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 20 in [1, 19] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 17 in [1, 2, 4, 8, 9, 13, 15, 16]) or
           (e = 2 and p mod 17 in [3, 5, 6, 7, 10, 11, 12, 14]) then
            # 2.L2_17
            LR := ReadAsFunction(Filename(CM_c9lib, "sl217d8.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p = 2 then
                    size := SizePSL(2, 17);
                else
                    size := 2 * SizePSL(2, 17);
                fi;
                SetSize(S[1], size);
            fi;
            if all and p <> 2 then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 2 then
            # S10
            LR := ReadAsFunction(Filename(CM_c9lib, "a10d9.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                size := 3628800;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
        fi;
        if p >= 11 then
            # 2.L2q
            S := AlmostSimpleDefiningCharacteristic_SymplecticSL2(8, q :
                                                                  normaliser := normaliser);
            if not normaliser then
                size := 2 * SizePSL(2, q);
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
        if IsOddInt(q) then
            S := AlmostSimpleDefiningCharacteristic_l2q3dim8(q :
                                                             normaliser := normaliser);
            if not normaliser then
                size := 2 * SizePSL(2, q^3) * 3;
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
    elif n = 10 then
        if novelties then return result; fi;
        if (e = 1 and p mod 16 in [1, 7, 9, 15]) or
           (e = 2 and p mod 16 in [3, 5, 11, 13] and p <> 3) then
            # 2.A6.2_2 if p mod 16 in [1, 15], 2.A6 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "2a6d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 16 in [1, 15] then
                    size := 1440;
                else
                    size := 720;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 16 in [1, 15] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 8 in [1, 3, 5, 7] and p <> 11) then
            # 2.L2_11.2 if p mod 8 in [1, 7], 2.L2_11 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "sl211d10a.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 8 in [1, 7] then
                    size := 2 * SizePSL(2, 11) * 2;
                else
                    size := 2 * SizePSL(2, 11);
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 8 in [1, 7] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 24 in [1, 11, 13, 23] and p <> 11) or
           (e = 2 and p mod 24 in [5, 7, 17, 19]) then
            # 2.L2_11 if p mod 24 in [11, 13], 2.L2_11.2 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "sl211d10b.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 24 in [11, 13] then
                    size := 2 * SizePSL(2, 11);
                else
                    size := 2 * SizePSL(2, 11) * 2;
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all and p mod 24 in [1, 5, 7, 17, 19, 23] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
                Append(result, [S[2], S[2] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if (e = 1 and p mod 8 in [1, 3, 5, 7]) then
            # U52.2 if p mod 8 in [1, 7], U52 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "u52d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 8 in [1, 7] then
                    size := 2 * SizePSU(5, 2) * 2;
                else
                    size := SizePSU(5, 2) * 2;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 8 in [1, 7] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if p >= 11 then
            # 2.L2q
            S := AlmostSimpleDefiningCharacteristic_SymplecticSL2(10, q :
                                                                  normaliser := normaliser);
            if not normaliser then
                size := 2 * SizePSU(2, q);
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
    elif n = 12 then
        if novelties then return result; fi;
        if (e = 1 and p mod 5 in [1, 4] and p <> 11) or
           (e = 2 and p mod 5 in [2, 3] and p <> 4) then
            # 2.L2_11.2 (q mod 20 in [1, 19]), 2.L2_11 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "sl211d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if q mod 20 in [1, 19] then
                    size := 2 * SizePSL(2, 11) * 2;
                else
                    size := 2 * SizePSL(2, 11);
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
            fi;
            if all and p mod 20 in [1, 19] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
                Append(result, [S[2], S[2] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
                Add(result, S[2]);
            fi;
        fi;
        if (e = 1 and p mod 7 in [1, 6] and p <> 13) or
           (e = 3 and p mod 7 in [2, 3, 4, 5]) then
            # 2.L2_13.2 (q mod 28 in [1, 27]), 2.L2_13 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "sl213d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if (e = 1 and p mod 28 in [1, 27] or e = 3) then
                    size := 2 * SizePSL(2, 13) * 2;
                else
                    size := 2 * SizePSL(2, 13);
                fi;
                SetSize(S[1], size);
                SetSize(S[2], size);
                SetSize(S[3], size);
            fi;
            if all and p mod 28 in [1, 27] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
                Append(result, [S[2], S[2] ^ generatorNormSpMinusSp]);
                Append(result, [S[3], S[3] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
                Add(result, S[2]);
                Add(result, S[3]);
            fi;
        fi;
        if (e = 1 and p mod 5 in [2, 3] and p <> 3) then
            # 2.L2_25 (p <> 2), L2_25.2 (p = 2)
            LR := ReadAsFunction(Filename(CM_c9lib, "sl225d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p <> 2 then
                    size := 2 * SizePSL(2, 25);
                else
                    size := SizePSL(2, 25) * 2;
                fi;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
        fi;
        if (e = 1 and p mod 5 in [0, 1, 4]) or
           (e = 2 and p mod 5 in [2, 3]) then
            # Sp4_5 (p <> 2) or PSp4_5 (p = 2)
            LR := ReadAsFunction(Filename(CM_c9lib, "sp45d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p <> 2 then
                    size := SizeSp(4, 5);
                else
                    size := SizePSp(4, 5);
                fi;
                SetSize(S[1], size);
            fi;
            if all and p <> 2 and p <> 5 then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p <> 2 and p <> 3) then
            # 2.G24.2 (p mod 8 in [1, 7]), 2.G24 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "2g24d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                if p mod 8 in [1, 7] then
                    size := 2 * Size(ChevalleyG(4)) * 2;
                else
                    size := 2 * Size(ChevalleyG(4));
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 8 in [1, 7] then
                Append(result, [S[1], S[1] ^ generatorNormSpMinusSp]);
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 3 then
            # 2.Suz
            LR := ReadAsFunction(Filename(CM_c9lib, "6suzd12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                size := 896690995200;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
        fi;
        if q = 2 then
            # S_14
            LR := ReadAsFunction(Filename(CM_c9lib, "a14d13.g"))();
            S := ModularReductionOfIntegralLattice(LR, q : normaliser := normaliser);
            if not normaliser then
                size := 87178291200;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
        fi;
        if p >= 13 then
            # 2.L2q
            S := AlmostSimpleDefiningCharacteristic_SymplecticSL2(12, q :
                                                                  normaliser := normaliser);
            if not normaliser then
                size := 2 * SizePSL(2, q);
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
    fi;
    return result;
end);

InstallGlobalFunction(MaximalSubgroupClassRepsSymplecticGroup,
function(n, q, classes...)
    local maximalSubgroups;

    if Length(classes) = 0 then
        classes := [1..9];
    elif Length(classes) = 1 and IsList(classes[1]) then
        classes := classes[1];
    fi;
    if not IsSubset([1..9], classes) then
        ErrorNoReturn("<classes> must be a subset of [1..9]");
    fi;


    if n = 2 then
        Error("We assume <n> to be greater or equal to 4 in case 'S' since",
              "Sp(2, q) and SL(2, q) are isomorphic");
    fi;

    if n = 4 and q = 2 then
        Error("Sp(4, 2) is not quasisimple");
    fi;

    maximalSubgroups := [];

    if 1 in classes then
        # Class C1 subgroups ######################################################
        # Cf. Propositions 3.3.1 (n = 4), 3.5.1 (n = 6), 3.7.1 (n = 8),
        #                  3.9.1 (n = 10), 3.11.1 (n = 12) in [BHR13]
        Append(maximalSubgroups, C1SubgroupsSymplecticGroupGeneric(n, q));
    fi;

    if 2 in classes then
        # Class C2 subgroups ######################################################
        # Cf. Propositions 3.3.3 (n = 4), 3.5.3, 3.5.4 (all n = 6),
        #                  3.7.3, 3.7.4 (all n = 8), 3.9.3, 3.9.4 (all n = 10),
        #                  3.11.3, 3.11.4, 3.11.5, 3.11.6 (all n = 12) in [BHR13]
        if not (n = 4 and q = 3) then
            Append(maximalSubgroups, C2SubgroupsSymplecticGroupGeneric(n, q));
        else
            Add(maximalSubgroups, SpNonDegenerateImprimitives(n, q, 2));
        fi;
    fi;

    if 3 in classes then
        # Class C3 subgroups ######################################################
        # Cf. Propositions 3.3.4 (n = 4), 3.5.5 (n = 6), 3.7.5 (n = 8),
        #                  3.9.5 (n = 10), 3.11.7 (n = 12) in [BHR13]
        if not (n = 4 and q = 3) then
            Append(maximalSubgroups, C3SubgroupsSymplecticGroupGeneric(n, q));
        else
            Add(maximalSubgroups, SymplecticSemilinearSp(n, q, 2));
        fi;
    fi;

    if 4 in classes then
        # Class C4 subgroups ######################################################
        # Cf. Propositions 3.5.6 (n = 6), 3.7.7 (n = 8), 3.9.6 (n = 10)
        #                  3.11.8 (n = 12) in [BHR13]
        # For n = 4, class C4 is empty.
        if n = 8 and IsOddInt(q) then
            # Cf. Lemma 3.7.6 in [BHR13]
            Add(maximalSubgroups, TensorProductStabilizerInSp(-1, 2, 4, q));
        elif n = 12 and q = 3 then
            Add(maximalSubgroups, TensorProductStabilizerInSp(1, 2, 6, q));
            Add(maximalSubgroups, TensorProductStabilizerInSp(-1, 2, 6, q));
        elif not (n = 6 and q <= 3) and not (n = 10 and q = 2) then
            Append(maximalSubgroups, C4SubgroupsSymplecticGroupGeneric(n, q));
        fi;
    fi;

    if 5 in classes then
        # Class C5 subgroups ######################################################
        # Cf. Propositions 3.3.5 (n = 4), 3.5.7 (n = 6), 3.7.8 (n = 8),
        #                  3.9.7 (n = 10), 3.11.9 (n = 12) in [BHR13]
        Append(maximalSubgroups, C5SubgroupsSymplecticGroupGeneric(n, q));
    fi;

    if 6 in classes then
        # Class C6 subgroups ######################################################
        # Cf. Propositions 3.3.6 (n = 4), 3.7.9 (n = 8) in [BHR13]
        # For all other n, class C6 is empty.
        Append(maximalSubgroups, C6SubgroupsSymplecticGroupGeneric(n, q));
    fi;

    if 7 in classes then
        # Class C7 subgroups ######################################################
        # Cf. Proposition 3.7.10 (n = 8) in [BHR13]
        # For all other n, class C7 is empty.
        Append(maximalSubgroups, C7SubgroupsSymplecticGroupGeneric(n, q));
    fi;

    if 8 in classes then
        # Class C8 subgroups ######################################################
        # Cf. Propositions 3.3.7 (n = 4), 3.5.8 (n = 6), 3.7.11 (n = 8),
        #                  3.9.8 (n = 10), 3.11.10 (n = 12) in [BHR13]
        if IsEvenInt(q) then
            Append(maximalSubgroups, C8SubgroupsSymplecticGroupGeneric(n, q));
        fi;
    fi;

    if 9 in classes then
        # Class C9 subgroups ######################################################
        # Cf. Theorems 4.10.13 (n = 4), 4.10.14 (n = 6), 4.10.15 (n = 8),
        #              4.10.16 (n = 10), 4.10.17 (n = 12) in [BHR13]
        # Cf. Theorems 5.11.6 (n = 4), 5.11.7 (n = 6), 5.11.8 (n = 8),
        #              5.11.10 (n = 10), 5.11.10 (n = 12) in [BHR13]
        # Cf. Tables 8.13, 8.14, 8.15 (all n = 4), 8.29 (n = 6),
        #            8.48 (n = 8), 8.65 (n = 10), 8.81 (n = 12) in [BHR13]
        Append(maximalSubgroups, C9SubgroupsSymplecticGroupGeneric(n, q));
    fi;

    return maximalSubgroups;

end);

# Return an element of SO(epsilon, n, q) \ Omega(epsilon, n, q)
InstallGlobalFunction("SOMinusOmega",
function(epsilon, n, q)
   return StandardGeneratorsOfOrthogonalGroup(epsilon, n, q).S; 
end);

# Return an element of GO(epsilon, n, q) \ SO(epsilon, n, q)
InstallGlobalFunction("GOMinusSO",
function(epsilon, n, q)
    if not IsOddInt(q) then
        ErrorNoReturn("<q> must be odd");
    fi;
    return StandardGeneratorsOfOrthogonalGroup(epsilon, n, q).G;
end);

# Return an element of Normaliser(GL(n, q), GO(epsilon, n, q)) \ GO(epsilon, n, q)
InstallGlobalFunction("NormGOMinusGO",
function(epsilon, n, q)
    return StandardGeneratorsOfOrthogonalGroup(epsilon, n, q).D;
end);

# Given a subgroup G of Omega(epsilon, n, q) conjugate it with all products of
# combinations of elements from the set ...
# * ... [SOMinusOmega(epsilon, n, q)] if numberOfConjugates = 2
# * ... [SOMinusOmega(epsilon, n, q), GOMinusSO(epsilon, n, q)] 
#       if numberOfConjugates = 4
# * ... [SOMinusOmega(epsilon, n, q), GOMinusSO(epsilon, n, q), NormGOMinusGO(epsilon, n, q)]
#       if numberOfConjugates = 8.
BindGlobal("ConjugateSubgroupOmega",
function(epsilon, n, q, G, numberOfConjugates)
    local elementsToConjugate, result, invariantFormRec,
    powerSet, subset, exponent, conjugatedGroup;

    if not numberOfConjugates in [1, 2, 4, 8] then
        ErrorNoReturn("<numberOfConjugates> must be one of 1, 2, 4, 8");
    fi;

    if numberOfConjugates = 1 then
        return [G];
    fi;

    elementsToConjugate := [SOMinusOmega(epsilon, n, q)];
    if numberOfConjugates >= 4 then
        Add(elementsToConjugate, GOMinusSO(epsilon, n, q));
        if numberOfConjugates = 8 then
            Add(elementsToConjugate, NormGOMinusGO(epsilon, n, q));
        fi;
    fi;

    result := [];
    invariantFormRec := InvariantQuadraticForm(G);
    powerSet := Combinations(elementsToConjugate);
    for subset in powerSet do
        if subset = [] then
            Add(result, G);
        else
            exponent := Product(subset);
            conjugatedGroup := G ^ exponent;
            SetInvariantQuadraticForm(conjugatedGroup, invariantFormRec);
            Add(result, conjugatedGroup);
        fi;
    od;

    return result;
end);
    
BindGlobal("C1SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local result, m, listOfks, G;

    result := [];

    m := QuoInt(n, 2);

    # Isotropic type, number of conjugates according to Proposition 4.1.20 (I) in [KL90]
    if epsilon = -1 then
        listOfks := [1..m - 1];
    elif epsilon = 0 then
        listOfks := [1..m];
    elif epsilon = 1 then
        listOfks := [1..m - 2];
        Add(listOfks, m);
        G := OmegaStabilizerOfIsotropicSubspace(epsilon, n, q, m - 1);
        Append(result, ConjugateSubgroupOmega(epsilon, n, q, G, 2));
    fi;
    Append(result, List(listOfks, k -> OmegaStabilizerOfIsotropicSubspace(epsilon, n, q, k)));

    # Non-degenerate type, number of conjugates according to Proposition 4.1.6 (I) in [KL90]
    if epsilon = 0 then

        listOfks := 2 * [1..m] - 1;
        Append(result, List(listOfks, k -> OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, -1, k)));

        # Cf. Proposition 2.3.2 (iii) in [BHR13]
        if q = 3 then
            RemoveSet(listOfks, n - 2);
        fi;
        Append(result, List(listOfks, k -> OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, 1, k)));

    else

        if IsOddInt(q) then
            listOfks := 2 * [1..QuoInt(m, 2)] - 1;
            Append(result, Flat(List(listOfks, k -> ConjugateSubgroupOmega(epsilon, n, q, OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, 0, k), 2))));
        fi;

        listOfks := 2 * [1..QuoInt(m - 1, 2)];

        if epsilon = -1 and IsEvenInt(m) then
            Add(result, OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, -1, m));
        fi;

        Append(result, List(listOfks, k -> OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, -1, k)));

        # Cf. Proposition 2.3.2 (iii) in [BHR13]
        if q in [2, 3] then
            RemoveSet(listOfks, 2);
        fi;

        Append(result, List(listOfks, k -> OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, 1, k)));

    fi;

    # Non-singular type, number of conjugates according to Proposition 4.1.7 (I) in [KL90]
    if IsEvenInt(q) then
        Add(result, OmegaStabilizerOfNonSingularVector(epsilon, n, q));
    fi;

    return result;
end);

BindGlobal("C2SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local result, squareDiscriminant, listOfms, genericPlusExceptions, numberOfConjugates, G, m, t;

    result := [];

    squareDiscriminant := epsilon = (-1) ^ QuoInt((q - 1) * n, 4);
    listOfms := Difference(DivisorsInt(n), [1, n]);

    # This case is nonmaximal according to Proposition 2.3.6 (x) in [BHR13]
    if q = 3 then
        listOfms := Difference(listOfms, [3]);
    fi;

    # These cases are also nonmaximal if epsilon = epsilon _0 = 1 according
    # to Proposition 2.3.6 (vii), (viii), (iv), (vi) in [BHR13]
    genericPlusExceptions := [[2, 2], [2, 3], [2, 4], [4, 2]];

    # Non-degenerate type with m = 1, this case needs special treatment
    # according to Proposition 4.2.15 in [KL90]
    if IsPrimeInt(q) and q <> 2 and (IsOddInt(n) or squareDiscriminant) then
        numberOfConjugates := Gcd(2, n);
        if q mod 8 in [1, 7] then
            numberOfConjugates := 2 * numberOfConjugates;
        fi;
        G := OmegaNonDegenerateImprimitives(epsilon, n, q, 0, n);
        Append(result, ConjugateSubgroupOmega(epsilon, n, q, G, numberOfConjugates));
    fi;

    # Non-degenerate type with m > 1
    for m in listOfms do

        t := QuoInt(n, m);

        if IsEvenInt(m) then
            # number of conjugates according to Proposition 4.2.11 (I) in [KL90]
            if epsilon = 1 and not (m, q) in genericPlusExceptions then
                Add(result, OmegaNonDegenerateImprimitives(epsilon, n, q, 1, t));
            fi;
            if (-1) ^ t = epsilon then
                Add(result, OmegaNonDegenerateImprimitives(epsilon, n, q, -1, t));
            fi;
        elif (IsOddInt(t) or squareDiscriminant) and IsOddInt(q) then
            # number of conjugates according to Proposition 4.2.14 (I) in [KL90]
            G := OmegaNonDegenerateImprimitives(epsilon, n, q, 0, t);
            Append(result, ConjugateSubgroupOmega(epsilon, n, q, G, Gcd(2, t)));
        fi;

    od;


    if IsEvenInt(n) then

        # Isotropic type, number of conjugates according to Proposition 4.2.7 (I) in [KL90]
        if epsilon = 1 then
            G := OmegaIsotropicImprimitives(n, q);
            Append(result, ConjugateSubgroupOmega(epsilon, n, q, G, Gcd(2, QuoInt(n, 2))));
        fi;

        # Non-degenerate non-isometric type, number of conjugates is 1 according to Proposition 4.2.16 (I) in [KL90]
        if not squareDiscriminant and IsOddInt(q * QuoInt(n, 2)) then
            Add(result, OmegaNonIsometricImprimitives(epsilon, n, q));
        fi;

    fi;

    return result;
end);

# Cf. Tables 3.5.D, 3.5.E, 3.5.F and 3.5.G in [KL90]
BindGlobal("C3SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local result, primeDivisorsOfn, s, orthogonalTypeSubgroup, numberOfConjugates,
    unitaryTypeSubgroup;

    result := [];
    primeDivisorsOfn := PrimeDivisors(n);

    # type GO(epsilon, n / s, q ^ s)
    for s in primeDivisorsOfn do
        if not n / s > 2 then 
            continue;
        fi;

        if s = 2 then
            if not n mod 4 = 0 then
                continue;
            else
                orthogonalTypeSubgroup := OrthogonalSemilinearOmega(epsilon, epsilon, n, q);
                if epsilon = 1 then
                    numberOfConjugates := 2;
                else
                    numberOfConjugates := 1;
                fi;
                Append(result, ConjugateSubgroupOmega(epsilon, n, q,
                                                      orthogonalTypeSubgroup,
                                                      numberOfConjugates));
            fi;
        else
            orthogonalTypeSubgroup := GammaLMeetOmega(epsilon, n, q, s);
            Add(result, orthogonalTypeSubgroup);
        fi;
    od;

    # type GO(0, n / 2, q ^ 2)
    if n mod 4 = 2 and IsOddInt(q) then
        orthogonalTypeSubgroup := OrthogonalSemilinearOmega(epsilon, 0, n, q);
        if q mod 4 = 2 + epsilon then
            numberOfConjugates := 1;
        else    
            numberOfConjugates := 2;
        fi;
        Append(result, ConjugateSubgroupOmega(epsilon, n, q,
                                              orthogonalTypeSubgroup,
                                              numberOfConjugates));
    fi;

    # type GU(n / 2, q ^ 2)
    if (n mod 4 = 2 and epsilon = -1) or (n mod 4 = 0 and epsilon = 1) then
        unitaryTypeSubgroup := UnitarySemilinearOmega(n, q);
        if epsilon = 1 then
            numberOfConjugates := 2;
        else
            numberOfConjugates := 1;
        fi;
        Append(result, ConjugateSubgroupOmega(epsilon, n, q,
                                              unitaryTypeSubgroup,
                                              numberOfConjugates));
    fi;
    
    return result;
end);

BindGlobal("C4SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local result, listOfn1s, n1, n2, numberOfConjugates, listOfn1sFiltered, G;

    result := [];

    # These are the orthogonal type subgroups with epsilon_2 = 0
    if epsilon = 0 then

        listOfn1s := Filtered(DivisorsInt(n), n1 -> n1 * n1 < n);
        RemoveSet(listOfn1s, 1);

        # number of conjugates is 1 according to [KL90] Proposition 4.4.18 (I)
        Append(result, List(listOfn1s, n1 -> OrthogonalTensorProductStabilizerInOmega(0, 0, 0, n1, n2, q)));

    elif IsOddInt(q) then

        listOfn1s := Filtered(DivisorsInt(n), IsEvenInt);
        RemoveSet(listOfn1s, 2);

        # This is nonmaximal, see Proposition 2.3.22 (v) in [BHR13]
        if q = 3 then
            RemoveSet(listOfn1s, n / 3);
        fi;

        for n1 in listOfn1s do
            n2 := QuoInt(n, n1);
            if IsOddInt(n2) and n2 <> 1 then
                # number of conjugates is 1 according to [KL90] Proposition 4.4.17 (I)
                Add(result, OrthogonalTensorProductStabilizerInOmega(epsilon, epsilon, 0, n1, n2, q));
            fi;
        od;

    fi;

    
    if epsilon = 1 and n mod 4 = 0 then
        
        listOfn1s := 2 * DivisorsInt(QuoInt(n, 2));
        listOfn1sFiltered := Filtered(listOfn1s, n1 -> n1 * n1 < n);

        # These are the orthogonal type subgroups with epsilon_i <> 0
        if IsOddInt(q) then

            # This is epsilon_1 = epsilon_2
            for n1 in listOfn1sFiltered do
                n2 := QuoInt(n, n1);
                if IsEvenInt(n2) and n1 <> 2 and n2 <> 2 then
                    # number of conjugates according to [KL90] Proposition 4.4.14 (I)
                    if n mod 8 = 4 or (q mod 4 = 3 and (n1 mod 4 = 2 or n2 mod 4 = 2)) then
                        numberOfConjugates := 2;
                    else
                        numberOfConjugates := 4;
                    fi;
                    G := OrthogonalTensorProductStabilizerInOmega(1, 1, 1, n1, n2, q);
                    Append(result, ConjugateSubgroupOmega(1, n, q, G, numberOfConjugates));
                    # number of conjugates according to [KL90] Proposition 4.4.16 (I)
                    G := OrthogonalTensorProductStabilizerInOmega(1, -1, -1, n1, n2, q);
                    Append(result, ConjugateSubgroupOmega(1, n, q, G, 2));
                fi;
            od;

            # This is epsilon_1 = 1, epsilon_2 = -1
            for n1 in listOfn1s do
                n2 := QuoInt(n, n1);
                if IsEvenInt(n2) and n1 <> 2 and n2 <> 2 then
                    # number of conjugates according to [KL90] Proposition 4.4.15 (I)
                    G := OrthogonalTensorProductStabilizerInOmega(1, 1, -1, n1, n2, q);
                    Append(result, ConjugateSubgroupOmega(1, n, q, G, 3 - (-1) ^ QuoInt((n1 - 2) * n2 * (q - 1), 8)));
                fi;
            od;

        fi;

        # These are the symplectic type subgroups
        
        # This is nonmaximal, see Proposition 2.3.22 (iv) in [BHR13]
        if q = 2 then
            RemoveSet(listOfn1sFiltered, 2);
        fi;

        # number of conjugates according to [KL90] Proposition 4.4.12 (I)
        numberOfConjugates := 3 - (-1) ^ (q * QuoInt(n - 4, 4));
        for n1 in listOfn1sFiltered do
            n2 := QuoInt(n, n1);
            if IsEvenInt(n2) then
                G := SymplecticTensorProductStabilizerInOmega(n1, n2, q);
                Append(result, ConjugateSubgroupOmega(1, n, q, G, numberOfConjugates));
            fi;
        od;

    fi;

    return result;
end);

BindGlobal("C5SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local factorisationOfq, p, e, listOfrs, result, G,
    numberOfConjugatesPlus, numberOfConjugatesMinus, r;

    factorisationOfq := PrimePowersInt(q);
    p := factorisationOfq[1];
    e := factorisationOfq[2];

    listOfrs := PrimeDivisors(e);
    result := [];

    if epsilon = 0 then

        # number of conjugates according to [KL90] Proposition 4.5.8 (I)
        if 2 in listOfrs then
            G := SubfieldOmega(0, n, p, e, QuoInt(e, 2), 0);
            Append(result, ConjugateSubgroupOmega(epsilon, n, q, G, 2));
            listOfrs := Difference(listOfrs, [2]);
        fi;

    else

        if 2 in listOfrs then

            # number of conjugates according to [KL90] Proposition 4.5.10 (I)
            if epsilon = 1 then
                if IsEvenInt(q) then
                    numberOfConjugatesPlus := 1;
                    numberOfConjugatesMinus := 1;
                elif n mod 4 = 2 and p ^ QuoInt(e, 2) mod 4 = 1 then
                    numberOfConjugatesPlus := 2;
                    numberOfConjugatesMinus := 4;
                else
                    numberOfConjugatesPlus := 4;
                    numberOfConjugatesMinus := 2;
                fi;
                G := SubfieldOmega(1, n, p, e, QuoInt(e, 2), 1);
                Append(result, ConjugateSubgroupOmega(epsilon, n, q, G, numberOfConjugatesPlus));
                G := SubfieldOmega(1, n, p, e, QuoInt(e, 2), -1);
                Append(result, ConjugateSubgroupOmega(epsilon, n, q, G, numberOfConjugatesMinus));
            fi;
            listOfrs := Difference(listOfrs, [2]);

        fi;

    fi;

    # The number of conjugates here is 1 according to [KL90] Proposition 4.5.8 (I)
    # and Proposition 4.5.10 (I) since r must now be odd.
    for r in listOfrs do
        Add(result, SubfieldOmega(epsilon, n, p, e, QuoInt(e, r), epsilon));
    od;

    return result;
end);

BindGlobal("C6SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local factorisationOfq, p, e, factorisationOfn, r, m, result,
    numberOfConjugates, extraspecialNormalizerSubgroup;

    if IsEvenInt(q) then
        return [];
    fi;

    if not IsPrimePowerInt(n) then
        return [];
    fi;

    result := [];
    
    factorisationOfq := PrimePowersInt(q);
    p := factorisationOfq[1];
    e := factorisationOfq[2];
    factorisationOfn := PrimePowersInt(n);
    r := factorisationOfn[1];
    m := factorisationOfn[2];

    # Cf. Table 4.6.B and the corresponding definition in [KL90]
    if epsilon = 1 and r = 2 and e = 1 then
        extraspecialNormalizerSubgroup := ExtraspecialNormalizerInOmega(m, q);
        # Cf. Tables 3.5.E and 3.5.G in [KL90]
        if (q - 1) mod 8 = 0  or (q - 7) mod 8 = 0 then
            numberOfConjugates := 8;    
        else
            numberOfConjugates := 4;
        fi;
        result := ConjugateSubgroupOmega(epsilon, n, q,
                                         extraspecialNormalizerSubgroup,
                                         numberOfConjugates);
    fi;

    return result;
end);

BindGlobal("C7SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local primeDivs, result, listOfts, t, m, numberOfConjugates, G, gcd;

    primeDivs := PrimePowersInt(n);
    if Length(primeDivs) <> 2 then
        return [];
    fi;

    result := [];

    listOfts := DivisorsInt(primeDivs[2]);
    listOfts := Difference(listOfts, [1]);

    if IsOddInt(n) then

        # Cf. [KL90] Proposition 4.7.8 (I)
        if q = 3 and primeDivs[1] = 3 then
            RemoveSet(listOfts, primeDivs[2]);
        fi;

        for t in listOfts do
            # number of conjugates is 1 according to [KL90] Proposition 4.7.8 (I)
            m := primeDivs[1] ^ QuoInt(primeDivs[2], t);
            Add(result, OrthogonalOddTensorInducedDecompositionStabilizerInOmega(m, t, q));
        od;

    elif epsilon = 1 then

        for t in listOfts do

            m := primeDivs[1] ^ QuoInt(primeDivs[2], t);

            if m >= 6 then

                # number of conjugates according to [KL90] Proposition 4.7.6 (I)
                if t = 2 and m mod 4 = 2 then
                    numberOfConjugates := 1;
                elif t = 3 and m mod 4 = 2 and q mod 4 = 3 then
                    numberOfConjugates := 2;
                else
                    numberOfConjugates := 4;
                fi;

                G := OrthogonalEvenTensorInducedDecompositionStabilizerInOmega(1, m, t, q);
                Append(result, ConjugateSubgroupOmega(1, n, q, G, numberOfConjugates));

            fi;

            if m >= 4 then

                # number of conjugates according to [KL90] Proposition 4.7.7 (I)
                if t = 2 and m mod 4 = 2 then
                    numberOfConjugates := 1;
                elif t = 2 and m mod 4 = 4 then
                    numberOfConjugates := 2;
                elif t = 3 and m mod 4 = 2 and q mod 4 = 3 then
                    numberOfConjugates := 2;
                else
                    numberOfConjugates := 4;
                fi;

                G := OrthogonalEvenTensorInducedDecompositionStabilizerInOmega(-1, m, t, q);
                Append(result, ConjugateSubgroupOmega(1, n, q, G, numberOfConjugates));

            fi;

        od;

        # Cf. [KL90] Proposition 4.7.5 (I)
        if q in [2, 3] and primeDivs[1] = 3 then
            RemoveSet(listOfts, primeDivs[2]);
        fi;

        gcd := Gcd(2, q - 1);
        for t in listOfts do

            m := primeDivs[1] ^ QuoInt(primeDivs[2], t);

            if IsEvenInt(q * t) then

                # number of conjugates according to [KL90] Proposition 4.7.5 (I)
                if t = 2 and m mod 4 = 2 then
                    numberOfConjugates := 1;
                else
                    numberOfConjugates := gcd;
                fi;

                G := SymplecticTensorInducedDecompositionStabilizerInOmega(m, t, q);
                Append(result, ConjugateSubgroupOmega(1, n, q, G, numberOfConjugates));

            fi;

        od;

    fi;

    return result;
end);

BindGlobal("C9SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local all, novelties, special, general, normaliser, ConjugatesBySubsetsOfGenerators,
          result, factorisation, p, e, generatorSOMinusOmega, generatorGOMinusSO,
          generatorNormGOMinusGO, LR, S, size, elementsToConjugate;

    all := ValueOption("all");
    if all = fail then all := true; fi;
    novelties := ValueOption("novelties");
    if novelties = fail then novelties := false; fi;
    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;

    # TODO This should be moved to a more appropriate location.
    #################################################
    if epsilon = 0 and IsEvenInt(n) then
        ErrorNoReturn("Degree must be odd for type \"O\"");
    elif epsilon <> 0 and IsOddInt(n) then
        ErrorNoReturn("Degree must be even for types \"O+\" or \"O-\"");
    fi;
    ################################################

    ConjugatesBySubsetsOfGenerators := function(G, gens)
        local result, powerSet, subset;
        result := [];
        powerSet := Combinations(gens);
        for subset in powerSet do
            if subset = [] then
                Add(result, G);
            else
                Add(result, G ^ Product(subset));
            fi;
        od;
        return result;
    end;

    result := [];
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorSOMinusOmega := SOMinusOmega(epsilon, n, q);
    if IsOddInt(q) then
        generatorGOMinusSO := GOMinusSO(epsilon, n, q);
        if IsEvenInt(n) then
            generatorNormGOMinusGO := NormGOMinusGO(epsilon, n, q);
        fi;
    fi;

    if n = 3 then
        if novelties then return result; fi;
        if (e = 1 and p mod 5 in [1, 4]) or
           (e = 2 and p <> 2 and p mod 5 in [2, 3]) then
            # A5
            LR := ReadAsFunction(Filename(CM_c9lib, "a5d3.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := 60;
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 4 then
        # must have epsilon -1
        if novelties then return result; fi;
        if (e = 1 and p <> 2 and p mod 5 in [2, 3]) then
            # A5
            LR := ReadAsFunction(Filename(CM_c9lib, "a5d4.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := 60;
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
    elif n = 5 then
        if novelties then
            if q = 7 then
                # L2q
                S := AlmostSimpleDefiningCharacteristic_OrthogSL2(5, q :
                                                                  special := special,
                                                                  general := general,
                                                                  normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := SizePSL(2, q);
                    SetSize(S, size);
                fi;
                Add(result, S);
            fi;
            return result;
        fi;
        if (e = 1 and p <> 7 and p mod 12 in [1, 5, 7, 11]) then
            # A6 (p mod 12 in [5, 7]) or S6 (p mod 12 in [1, 11])
            LR := ReadAsFunction(Filename(CM_c9lib, "a6d5.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                if p mod 12 in [5, 7] then
                    size := 360;
                else
                    size := 720;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 12 in [1, 11] then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 7 then
            # A7
            LR := ReadAsFunction(Filename(CM_c9lib, "a7d6.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := 2520;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
        fi;
        if p >= 5 and q > 7 then
            # L2q
            S := AlmostSimpleDefiningCharacteristic_OrthogSL2(5, q :
                                                              special := special,
                                                              general := general,
                                                              normaliser := normaliser);
            if not special and not general and not normaliser then
                size := SizePSL(2, q);
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
    elif n = 6 then
        if novelties then
            if e = 1 and ((epsilon = 1 and p mod 7 in [1, 2, 4]) or
                          (epsilon = -1 and p mod 7 in [3, 5, 6])) then
                # L_2(7)
                LR := ReadAsFunction(Filename(CM_c9lib, "l27d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    if epsilon = 1 then
                        size := QuoInt(Gcd(q - 1, 4), 2) * SizePSL(2, 7);
                    else
                        size := QuoInt(Gcd(q + 1, 4), 2) * SizePSL(2, 7);
                    fi;
                    SetSize(S[1], size);
                fi;
                if all and q mod 4 = 1 then
                    if epsilon = -1 then
                        elementsToConjugate := [generatorNormGOMinusGO];
                    else
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorNormGOMinusGO];
                    fi;
                elif all and q mod 4 = 3 then
                    if epsilon = 1 then
                        elementsToConjugate := [generatorNormGOMinusGO];
                    else
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorNormGOMinusGO];
                    fi;
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            return result;
        fi;
        if epsilon = 1 then
            if e = 1 and p mod 7 in [1, 2, 4] then
                # A7
                LR := ReadAsFunction(Filename(CM_c9lib, "a7d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    if p = 2 then
                        size := 2520;
                    else
                        size := QuoInt(Gcd(q - 1, 4), 2) * 2520;
                    fi;
                    SetSize(S[1], size);
                fi;
                if all and q mod 4 = 1 then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                elif all and q mod 4 = 3 then
                    elementsToConjugate := [generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if e = 1 and p mod 6 = 1 then
                # U42
                LR := ReadAsFunction(Filename(CM_c9lib, "u42d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := QuoInt(Gcd(q - 1, 4), 2) * SizePSU(4, 2);
                    SetSize(S[1], size);
                fi;
                if all and q mod 4 = 1 then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                elif all and q mod 4 = 3 then
                    elementsToConjugate := [generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
        elif epsilon = -1 then
            if e = 1 and p mod 7 in [3, 5, 6] then
                # A7
                LR := ReadAsFunction(Filename(CM_c9lib, "a7d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := QuoInt(Gcd(q + 1, 4), 2) * 2520;
                    SetSize(S[1], size);
                fi;
                if all and q mod 4 = 3 then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                elif all and q mod 4 = 1 then
                    elementsToConjugate := [generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if e = 1 and p mod 6 = 5 then
                # U42
                LR := ReadAsFunction(Filename(CM_c9lib, "u42d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := QuoInt(Gcd(q + 1, 4), 2) * SizePSU(4, 2);
                    SetSize(S[1], size);
                fi;
                if all and q mod 4 = 3 then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                elif all and q mod 4 = 1 then
                    elementsToConjugate := [generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if q = 3 then
                # 2.L34
                LR := ReadAsFunction(Filename(CM_c9lib, "6l34d6.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 2 * SizePSL(3, 4);
                    SetSize(S[1], size);
                fi;
                if all then
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorGOMinusSO]));
                else
                    Add(result, S[1]);
                fi;
            fi;
        fi;
    elif n = 7 then
        if novelties then return result; fi;
        if e = 1 then
            # Sp62
            LR := ReadAsFunction(Filename(CM_c9lib, "s62d7.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := SizeSp(6, 2);
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 3 then
            # S9
            LR := ReadAsFunction(Filename(CM_c9lib, "a9d8.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := 362880;
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        S := ChevalleyG(q);
        S := ConjugateToStandardForm(S, "O", GF(q));
        if normaliser then
            S := Group(Concatenation(GeneratorsOfGroup(S),
                                     [PrimitiveElement(GF(q)) * IdentityMat(n, Integers)]));
        elif general then
            S := Group(Concatenation(GeneratorsOfGroup(S),
                                     [(-1)*One(GF(q)) * IdentityMat(n, Integers)]));
        fi;
        if all then
            Append(result, ConjugatesBySubsetsOfGenerators(S, [generatorSOMinusOmega]));
        else
            Add(result, S);
        fi;
    elif n = 8 then
        if epsilon = 1 then
            if novelties then return result; fi;
            if (e = 1 and p >= 3) then
                # 2.Omega+(8,2)
                LR := ReadAsFunction(Filename(CM_c9lib, "2o8+2d8.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 2 * SizeOmega(1, 8, 2);
                    SetSize(S[1], size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if q = 2 then
                # A9 x3 (all fused under triality)
                LR := ReadAsFunction(Filename(CM_c9lib, "a9d8.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 181440;
                    SetSize(S[1], size);
                fi;
                Add(result, S[1]);
                LR := ReadAsFunction(Filename(CM_c9lib, "2a9d8.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 181440;
                    SetSize(S[1], size);
                fi;
                if all then
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
                else
                    Add(result, S[1]);
                fi;
            fi;
            if q = 5 then
                # A10, 2.A10 (all fused under triality)
                LR := ReadAsFunction(Filename(CM_c9lib, "a10d9.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 3628800;
                    SetSize(S[1], size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                LR := ReadAsFunction(Filename(CM_c9lib, "2a10d16.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 3628800;
                    SetSize(S[1], size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorGOMinusSO,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                # 2Sz8
                S := ReadAsFunction(Filename(CM_c9lib, "2sz8d8f5.g"))();
                if normaliser then
                    S := GroupByGenerators(Concatenation(GeneratorsOfGroup(S),
                                                         [PrimitiveElement(GF(q))
                                                          * IdentityMat(5, Integers)]));
                fi;
                if not special and not general and not normaliser then
                    size := 58240;
                    SetSize(S, size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorGOMinusSO,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S, elementsToConjugate));
            fi;
            if (q <> 2 and p <> 3) then
                # PSL(3,q).3 or PSU(3,q).3
                if q mod 3 = 1 then
                    S := AlmostSimpleDefiningCharacteristic_l3qdim8(q :
                                                                    special := special,
                                                                    general := general,
                                                                    normaliser := normaliser);
                else
                    S := AlmostSimpleDefiningCharacteristic_u3qdim8(q :
                                                                    special := special,
                                                                    general := general,
                                                                    normaliser := normaliser);
                fi;
                if not special and not general and not normaliser then
                    if q mod 3 = 1 then
                        size := Gcd(q - 1, 2) * SizePSL(3, q) * 3;
                    else
                        size := Gcd(q - 1, 2) * SizePSU(3, q) * 3;
                    fi;
                    SetSize(S, size);
                fi;
                if all and IsOddInt(q) then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S, elementsToConjugate));
            fi;
            if e mod 3 = 0 then
                S := Group(Concatenation(GeneratorsOfGroup(Chevalley3D4(RootInt(q, 3))),
                                         [(-1)*One(GF(q)) * IdentityMat(8, Integers)]));
                S := ConjugateToStandardForm(S, "O+", GF(q));
                if not special and not general and not normaliser then
                    size := Gcd(q - 1, 2) * Size(Chevalley3D4(RootInt(q, 3)));
                    SetSize(S, size);
                fi;
                if all then
                    if p = 2 then
                        elementsToConjugate := [generatorSOMinusOmega];
                    else
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorGOMinusSO,
                                                generatorNormGOMinusGO];
                    fi;
                    Append(result, ConjugatesBySubsetsOfGenerators(S, elementsToConjugate));
                else
                    Add(result, S);
                fi;
            fi;
            # 2.O(7,q)
            if normaliser and p <> 2 then
                Info(InfoWarning, 1, "2.O(7,q).2 < N_{GL(8,q)}(O^+(8,q))",
                                     " is not implemented yet.");
            else
                Info(InfoWarning, 1, "2.O(7,q) < O^+(8,q) is not implemented yet.");
            fi;
            # if normaliser and p <> 2 then
            #     S := TwoO72(q);
            # else
            #     S := TwoO7(q);
            # fi;
            # if normaliser and p = 2 then
            #     S := GroupByGenerators(Concatenation(GeneratorsOfGroup(S),
            #                                          [PrimitiveElement(GF(q))
            #                                           * IdentityMat(8, Integers)]));
            # fi;
            # if not special and not general and not normaliser then
            #     if p = 2 then
            #         size := SizeOmega(0, 7, q);
            #     else
            #         size := 2 * SizeOmega(0, 7, q);
            #     fi;
            #     SetSize(S, size);
            # fi;
            # if all then
            #     if p = 2 then
            #         elementsToConjugate := [generatorSOMinusOmega];
            #     else
            #         elementsToConjugate := [generatorSOMinusOmega,
            #                                 generatorGOMinusSO];
            #     fi;
            #     Append(result, ConjugatesBySubsetsOfGenerators(S, elementsToConjugate));
            # else
            #     Add(result, S);
            # fi;
            if IsEvenInt(e) then
                # 2.O^-(8,q^(1/2))
                if normaliser and p <> 2 then
                    Info(InfoWarning, 1, "2.O^-(8,q^(1/2)).2 < N_{GL(8,q)}(O^+(8,q))",
                                         " is not implemented yet.");
                else
                    Info(InfoWarning, 1, "2.O^-(8,q^(1/2)) < O^+(8,q)",
                                         " is not implemented yet.");
                fi;
                # if normaliser and p <> 2 then
                #     S := TwoOminus82(p ^ QuoInt(e, 2));
                # else
                #     S := TwoOminus8(p ^ QuoInt(e, 2));
                # fi;
                # if normaliser and p = 2 then
                #     S := GroupByGenerators(Concatenation(GeneratorsOfGroup(S),
                #                                          [PrimitiveElement(GF(q))
                #                                           * IdentityMat(8, Integers)]));
                # fi;
                # if not special and not general and not normaliser then
                #     if p = 2 then
                #         size := SizeOmega(-1, 8, p ^ QuoInt(e, 2));
                #     else
                #         size := 2 * SizeOmega(-1, 8, p ^ QuoInt(e, 2));
                #     fi;
                #     SetSize(S, size);
                # fi;
                # if all then
                #     if p = 2 then
                #         elementsToConjugate := [generatorSOMinusOmega];
                #     else
                #         elementsToConjugate := [generatorSOMinusOmega,
                #                                 generatorGOMinusSO];
                #     fi;
                #     Append(result, ConjugatesBySubsetsOfGenerators(S, elementsToConjugate));
                # else
                #     Add(result, S);
                # fi;
            fi;
        elif epsilon = -1 then
            if novelties then return result; fi;
            if p <> 3 then
                # PSL(3,q) or PSU(3,q)
                if q mod 3 = 2 then
                    S := AlmostSimpleDefiningCharacteristic_l3qdim8(q :
                                                                    special := special,
                                                                    general := general,
                                                                    normaliser := normaliser);
                else
                    S := AlmostSimpleDefiningCharacteristic_u3qdim8(q :
                                                                    special := special,
                                                                    general := general,
                                                                    normaliser := normaliser);
                fi;
                if not special and not general and not normaliser then
                    if q mod 3 = 2 then
                        size := SizePSL(3, q);
                    else
                        size := SizePSU(3, q);
                    fi;
                    SetSize(S, size);
                fi;
                if all and IsOddInt(q) then
                    Append(result, ConjugatesBySubsetsOfGenerators(S, [generatorNormGOMinusGO]));
                else
                    Add(result, S);
                fi;
            fi;
        fi;
    elif n = 9 then
        if novelties then return result; fi;
        if (e = 1 and p mod 7 in [1, 6]) or
           (e = 3 and p mod 7 in [2, 3, 4, 5]) then
            LR := ReadAsFunction(Filename(CM_c9lib, "l28d9.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := SizePSL(2, 8);
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p mod 17 in [1, 2, 4, 8, 9, 13, 15, 16]) or
           (e = 2 and p mod 17 in [3, 5, 6, 7, 10, 11, 12, 14]) then
            LR := ReadAsFunction(Filename(CM_c9lib, "l217d9.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := SizePSL(2, 17);
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        if (e = 1 and p <> 11 and p mod 5 <> 0) then
            # A10 (p mod 5 in [2, 3]) or A10.2 otherwise
            LR := ReadAsFunction(Filename(CM_c9lib, "a10d9.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                if p mod 5 in [2, 3] then
                    size := 1814400;
                else
                    size := 3628800;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 5 in [1, 4] then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 11 then
            # A11.2
            LR := ReadAsFunction(Filename(CM_c9lib, "a11d10.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := 39916800;
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        if p >= 11 then
            # L2q
            S := AlmostSimpleDefiningCharacteristic_OrthogSL2(9, q :
                                                              special := special,
                                                              general := general,
                                                              normaliser := normaliser);
            if not special and not general and not normaliser then
                size := SizePSL(2, q) * 2;
                SetSize(S, size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S, [generatorSOMinusOmega]));
            else
                Add(result, S);
            fi;
        fi;
        if q <> 3 then
            # L2q^2
            S := AlmostSimpleDefiningCharacteristic_l2q2dim9(q :
                                                             special := special,
                                                             general := general,
                                                             normaliser := normaliser);
            if not special and not general and not normaliser then
                size := SizePSL(2, q^2) * 2;
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
    elif n = 10 then
        if epsilon = 1 then
            if novelties then
                if (e = 1 and p mod 12 in [1, 5]) then
                    # A6
                    LR := ReadAsFunction(Filename(CM_c9lib, "a6d10.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        if p mod 12 = 1 then
                            size := 1440;
                        else
                            size := 720;
                        fi;
                        SetSize(S[1], size);
                    fi;
                    if all and p mod 12 = 1 then
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorNormGOMinusGO];
                    elif all and p mod 12 = 5 then
                        elementsToConjugate := [generatorNormGOMinusGO];
                    else
                        elementsToConjugate := [];
                    fi;
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                fi;
                if (e = 1 and p mod 11 in [1, 3, 4, 5, 9] and p <> 3) then
                    # L211b
                    LR := ReadAsFunction(Filename(CM_c9lib, "l211d10b.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        if p mod 4 = 1 then
                            size := 2 * SizePSL(2, 11);
                        else
                            size := SizePSL(2, 11);
                        fi;
                        SetSize(S[1], size);
                    fi;
                    if all and p mod 4 = 1 then
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorNormGOMinusGO];
                    elif all and p mod 4 = 3 then
                        elementsToConjugate := [generatorNormGOMinusGO];
                    else
                        elementsToConjugate := [];
                    fi;
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                fi;
                return result;
            fi;
            if (e = 1 and p mod 11 in [1, 3, 4, 5, 9] and p <> 3) then
                # L2_11a
                LR := ReadAsFunction(Filename(CM_c9lib, "l211d10a.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    if p mod 4 = 1 then
                        size := 2 * SizePSL(2, 11);
                    else
                        size := SizePSL(2, 11);
                    fi;
                    SetSize(S[1], size);
                fi;
                if all and p mod 4 = 1 then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                elif all and p mod 4 = 3 then
                    elementsToConjugate := [generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if (e = 1 and p mod 11 in [1, 3, 4, 5, 9] and p <> 3) then
                # A11
                LR := ReadAsFunction(Filename(CM_c9lib, "a11d10.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    if p mod 4 = 1 then
                        size := 39916800;
                    else
                        size := 19958400;
                    fi;
                    SetSize(S[1], size);
                fi;
                if all and p mod 4 = 1 then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                elif all and p mod 4 = 3 then
                    elementsToConjugate := [generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if q = 3 then
                # A12
                LR := ReadAsFunction(Filename(CM_c9lib, "a12d11.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 239500800;
                    SetSize(S[1], size);
                fi;
                if all then
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorNormGOMinusGO]));
                else
                    Add(result, S[1]);
                fi;
            fi;
            if q mod 4 = 1 then
                # Sp4q
                S := AlmostSimpleDefiningCharacteristic_sp4qdim10(q :
                                                                  special := special,
                                                                  general := general,
                                                                  normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 2 * SizePSp(4, q);
                    SetSize(S, size);
                fi;
                if all then
                    elementsToConjugate := [generatorGOMinusSO,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S, elementsToConjugate));
            fi;
        elif epsilon = -1 then
            if novelties then
                if (e = 1 and p mod 12 in [7, 11]) then
                    # A6
                    LR := ReadAsFunction(Filename(CM_c9lib, "a6d10.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        if p mod 12 = 7 then
                            size := 720;
                        else
                            size := 1440;
                        fi;
                        SetSize(S[1], size);
                    fi;
                    if all and p mod 12 = 11 then
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorNormGOMinusGO];
                    elif all and p mod 12 = 7 then
                        elementsToConjugate := [generatorNormGOMinusGO];
                    else
                        elementsToConjugate := [];
                    fi;
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                fi;
                if (e = 1 and p mod 11 in [2, 6, 7, 8, 10]) then
                    # L211b
                    # TODO is this subgroup really maximal for p = 2?
                    # see Proposition 4.9.62
                    LR := ReadAsFunction(Filename(CM_c9lib, "l211d10b.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        if p mod 4 = 3 then
                            size := 2 * SizePSL(2, 11);
                        else
                            size := SizePSL(2, 11);
                        fi;
                        SetSize(S[1], size);
                    fi;
                    if all and p mod 4 = 3 then
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorNormGOMinusGO];
                    elif all and p mod 4 = 1 then
                        elementsToConjugate := [generatorNormGOMinusGO];
                    else
                        elementsToConjugate := [];
                    fi;
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                fi;
                if q = 2 then
                    # M12
                    LR := ReadAsFunction(Filename(CM_c9lib, "m12d11.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        size := 95040;
                        SetSize(S[1], size);
                    fi;
                    Add(result, S[1]);
                fi;
                if q = 7 then
                    # 2L34d10
                    LR := ReadAsFunction(Filename(CM_c9lib, "2l34d10.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        size := 2 * SizePSL(3, 4);
                        SetSize(S[1], size);
                    fi;
                    if all then
                        Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorNormGOMinusGO]));
                    else
                        Add(result, S[1]);
                    fi;
                fi;
                return result;
            fi;
            if (e = 1 and p mod 11 in [2, 6, 7, 8, 10] and p <> 2) then
                # L2_11
                LR := ReadAsFunction(Filename(CM_c9lib, "l211d10a.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    if p mod 4 = 3 then
                        size := 2 * SizePSL(2, 11);
                    else
                        size := SizePSL(2, 11);
                    fi;
                    SetSize(S[1], size);
                fi;
                if all and p mod 4 = 3 then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                elif all and p mod 4 = 1 then
                    elementsToConjugate := [generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if (e = 1 and p mod 11 in [2, 6, 7, 8, 10] and p <> 2) then
                # A11
                LR := ReadAsFunction(Filename(CM_c9lib, "a11d10.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    if p mod 4 = 1 then
                        size := 19958400;
                    else
                        size := 39916800;
                    fi;
                    SetSize(S[1], size);
                fi;
                if all and p mod 4 = 3 then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                elif all and p mod 4 = 1 then
                    elementsToConjugate := [generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if q = 2 then
                # A12
                LR := ReadAsFunction(Filename(CM_c9lib, "a12d11.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 239500800;
                    SetSize(S[1], size);
                fi;
                Add(result, S[1]);
            fi;
            if q = 7 then
                # 2.M22
                LR := ReadAsFunction(Filename(CM_c9lib, "2m22d10.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 887040;
                    SetSize(S[1], size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if q mod 4 = 3 then
                # Sp4q
                S := AlmostSimpleDefiningCharacteristic_sp4qdim10(q :
                                                                  special := special,
                                                                  general := general,
                                                                  normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 2 * SizePSp(4, q);
                    SetSize(S, size);
                fi;
                if all then
                    elementsToConjugate := [generatorGOMinusSO,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S, elementsToConjugate));
            fi;
        fi;
    elif n = 11 then
        if (e = 1 and Gcd(p, 24) = 1 and p <> 13) then
            # A12 (p mod 24 in [7, 11, 13, 17]) or A12.2 (p mod 24 in [1, 5, 19, 23])
            LR := ReadAsFunction(Filename(CM_c9lib, "a12d11.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                if p mod 24 in [7, 11, 13, 17] then
                    size := 239500800;
                else
                    size := 479001600;
                fi;
                SetSize(S[1], size);
            fi;
            if all and p mod 24 in [1, 5, 19, 23] then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        if q = 13 then
            # A13
            LR := ReadAsFunction(Filename(CM_c9lib, "a13d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := 3113510400;
                SetSize(S[1], size);
            fi;
            Add(result, S[1]);
            # L33.2
            LR := ReadAsFunction(Filename(CM_c9lib, "l33d12.g"))();
            S := ModularReductionOfIntegralLattice(LR, q :
                                                   special := special,
                                                   general := general,
                                                   normaliser := normaliser);
            if not special and not general and not normaliser then
                size := SizePSL(3, 3) * 2;
                SetSize(S[1], size);
            fi;
            if all then
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorSOMinusOmega]));
            else
                Add(result, S[1]);
            fi;
        fi;
        if p >= 11 and q <> 11 then
            # L2q
            S := AlmostSimpleDefiningCharacteristic_OrthogSL2(11, q :
                                                              special := special,
                                                              general := general,
                                                              normaliser := normaliser);
            if not special and not general and not normaliser then
                size := SizePSL(2, q);
                SetSize(S, size);
            fi;
            Add(result, S);
        fi;
    elif n = 12 then
        if epsilon = 1 then
            if novelties then
                if (e = 1 and p mod 13 in [1, 3, 4, 9, 10, 12] and p <> 3) then
                    # L33
                    LR := ReadAsFunction(Filename(CM_c9lib, "l33d12.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        size := 2 * SizePSL(3, 3);
                        SetSize(S[1], size);
                    fi;
                    if all and p mod 12 in [1, 11] then
                        elementsToConjugate := [generatorGOMinusSO,
                                                generatorNormGOMinusGO];
                    elif all then
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorGOMinusSO];
                    else
                        elementsToConjugate := [];
                    fi;
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                fi;
                if (e = 1 and p >= 5 and p mod 24 in [5, 7, 11, 13, 17, 19]) then
                    # 2.M12
                    LR := ReadAsFunction(Filename(CM_c9lib, "2m12d12.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        size := 2 * 95040;
                        SetSize(S[1], size);
                    fi;
                    if all and p mod 24 in [11, 13] then
                        elementsToConjugate := [generatorGOMinusSO,
                                                generatorNormGOMinusGO];
                    elif all then
                        elementsToConjugate := [generatorSOMinusOmega,
                                                generatorGOMinusSO];
                    else
                        elementsToConjugate := [];
                    fi;
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                fi;
                return result;
            fi;
            if (e = 1 and p mod 55 in [1, 16, 19, 24, 26, 29, 31, 36, 39, 54]) then
                # L2_11
                LR := ReadAsFunction(Filename(CM_c9lib, "l211d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 2 * SizePSL(2, 11);
                    SetSize(S[1], size);
                    SetSize(S[2], size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                Append(result, ConjugatesBySubsetsOfGenerators(S[2], elementsToConjugate));
            fi;
            if (p mod 13 in [1, 3, 4, 9, 10, 12]) and
               ((e = 1 and p mod 7 in [1, 6]) or
                (e = 3 and p mod 7 in [2, 3, 4, 5])) then
                # L2_13
                LR := ReadAsFunction(Filename(CM_c9lib, "l213d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 2 * SizePSL(2, 13);
                    SetSize(S[1], size);
                    SetSize(S[2], size);
                    SetSize(S[3], size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
                Append(result, ConjugatesBySubsetsOfGenerators(S[2], elementsToConjugate));
                Append(result, ConjugatesBySubsetsOfGenerators(S[3], elementsToConjugate));
            fi;
            if (e = 1 and p mod 13 in [1, 3, 4, 9, 10, 12]) then
                # A13
                LR := ReadAsFunction(Filename(CM_c9lib, "a13d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 6227020800;
                    SetSize(S[1], size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if (e = 1 and p >= 5 and p mod 24 in [1, 23]) then
                # 2.M12.2
                LR := ReadAsFunction(Filename(CM_c9lib, "2m12d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 2 * 95040 * 2;
                    SetSize(S[1], size);
                fi;
                if all then
                    elementsToConjugate := [generatorSOMinusOmega,
                                            generatorGOMinusSO,
                                            generatorNormGOMinusGO];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
        elif epsilon = -1 then
            if novelties then
                if (e = 1 and p mod 13 in [2, 5, 6, 7, 8, 11] and p mod 12 in [5, 7]) then
                    # L33
                    LR := ReadAsFunction(Filename(CM_c9lib, "l33d12.g"))();
                    S := ModularReductionOfIntegralLattice(LR, q :
                                                           special := special,
                                                           general := general,
                                                           normaliser := normaliser);
                    if not special and not general and not normaliser then
                        size := SizePSL(3, 3);
                        SetSize(S[1], size);
                    fi;
                    if all then
                        Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorGOMinusSO]));
                    else
                        Add(result, S[1]);
                    fi;
                fi;
                return result;
            fi;
            if (e = 1 and p mod 55 in [4, 6, 9, 14, 21, 34, 41, 46, 49, 51]) or
               (e = 2 and p mod 5 in [2, 3]) then
                # L2_11
                LR := ReadAsFunction(Filename(CM_c9lib, "l211d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := SizePSL(2, 11);
                    SetSize(S[1], size);
                    SetSize(S[2], size);
                fi;
                if all and p <> 2 then
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorNormGOMinusGO]));
                    Append(result, ConjugatesBySubsetsOfGenerators(S[2], [generatorNormGOMinusGO]));
                else
                    Add(result, S[1]);
                    Add(result, S[2]);
                fi;
            fi;
            if (p mod 13 in [2, 5, 6, 7, 8, 11]) and
               ((e = 1 and p mod 7 in [1, 6]) or
                (e = 3 and p mod 7 in [2, 3, 4, 5])) then
                # L2_13
                LR := ReadAsFunction(Filename(CM_c9lib, "l213d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := SizePSL(2, 13);
                    SetSize(S[1], size);
                    SetSize(S[2], size);
                    SetSize(S[3], size);
                fi;
                if all and p <> 2 then
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorNormGOMinusGO]));
                    Append(result, ConjugatesBySubsetsOfGenerators(S[2], [generatorNormGOMinusGO]));
                    Append(result, ConjugatesBySubsetsOfGenerators(S[3], [generatorNormGOMinusGO]));
                else
                    Add(result, S[1]);
                    Add(result, S[2]);
                    Add(result, S[3]);
                fi;
            fi;
            if (e = 1 and p mod 13 in [2, 5, 6, 7, 8, 11] and p mod 12 in [1, 2, 11]) then
                # L33.2
                LR := ReadAsFunction(Filename(CM_c9lib, "l33d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := SizePSL(3, 3) * 2;
                    SetSize(S[1], size);
                fi;
                if all and p mod 12 in [1, 11] then
                    elementsToConjugate := [generatorGOMinusSO,
                                            generatorNormGOMinusGO];
                elif all and p = 2 then
                    elementsToConjugate := [generatorSOMinusOmega];
                else
                    elementsToConjugate := [];
                fi;
                Append(result, ConjugatesBySubsetsOfGenerators(S[1], elementsToConjugate));
            fi;
            if (e = 1 and p mod 13 in [2, 5, 6, 7, 8, 11] and p <> 7) then
                # A13
                LR := ReadAsFunction(Filename(CM_c9lib, "a13d12.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 3113510400;
                    SetSize(S[1], size);
                fi;
                if all and p <> 2 then
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorNormGOMinusGO]));
                else
                    Add(result, S[1]);
                fi;
            fi;
            if q = 7 then
                # A14
                LR := ReadAsFunction(Filename(CM_c9lib, "a14d13.g"))();
                S := ModularReductionOfIntegralLattice(LR, q :
                                                       special := special,
                                                       general := general,
                                                       normaliser := normaliser);
                if not special and not general and not normaliser then
                    size := 43589145600;
                    SetSize(S[1], size);
                fi;
                if all then
                    Append(result, ConjugatesBySubsetsOfGenerators(S[1], [generatorNormGOMinusGO]));
                else
                    Add(result, S[1]);
                fi;
            fi;
        fi;
    fi;
    return result;
end);

InstallGlobalFunction(MaximalSubgroupClassRepsOrthogonalGroup,
function(epsilon, n, q, classes...)
    local maximalSubgroups, squareDiscriminant, numberOfConjugates, G;

    if Length(classes) = 0 then
        classes := [1..9];
    elif Length(classes) = 1 and IsList(classes[1]) then
        classes := classes[1];
    fi;
    if not IsSubset([1..9], classes) then
        ErrorNoReturn("<classes> must be a subset of [1..9]");
    fi;


    if n < 7 then
        Error("We assume <n> to be greater or equal to 7 in case 'O' since",
              " otherwise Omega(epsilon, n, q) is either not quasisimple or",
              " isomorphic to another classical group");
    fi;

    maximalSubgroups := [];

    if 1 in classes then
        # Class C1 subgroups ######################################################
        # Cf. Propositions 3.6.1 (n = 7), 3.7.1 (n = 8), 3.8.1 (n = 9),
        # 3.9.1 (n = 10), 3.10.1 (n = 11), 3.11.1 (n = 12)
        # and Table 8.50 (n = 8) in [BHR13]
        Append(maximalSubgroups, C1SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
    fi;

    if 2 in classes then
        # Class C2 subgroups ######################################################
        # Cf. Propositions 3.6.2 (n = 7), 3.7.2, 3.7.3, 3.7.4 (all n = 8),
        # 3.8.2 (n = 9), 3.9.2, 3.9.3, 3.9.4 (all n = 10), 3.10.2 (n = 11),
        # 3.11.2, 3.11.3, 3.11.4, 3.11.5, 3.11.6 (all n = 12)
        # and Table 8.50 (n = 8) in [BHR13]
        if n = 10 then
            squareDiscriminant := epsilon = (-1) ^ QuoInt(q - 1, 2);
            if IsPrimeInt(q) and q <> 2 and squareDiscriminant then
                numberOfConjugates := 2;
                if q mod 8 in [1, 7] then
                    numberOfConjugates := 2 * numberOfConjugates;
                fi;
                G := OmegaNonDegenerateImprimitives(epsilon, 10, q, 0, 10);
                Append(maximalSubgroups, ConjugateSubgroupOmega(epsilon, n, q, G, numberOfConjugates));
            fi;
            if (epsilon = 1 and q > 5) or (epsilon = -1 and q <> 3) then
                Add(maximalSubgroups, OmegaNonDegenerateImprimitives(epsilon, 10, q, epsilon, 5));
            fi;
            if IsOddInt(q) then
                if squareDiscriminant then
                    G := OmegaNonDegenerateImprimitives(epsilon, 10, q, 0, 2);
                    Append(maximalSubgroups, ConjugateSubgroupOmega(epsilon, 10, q, G, 2));
                else
                    Add(maximalSubgroups, OmegaNonIsometricImprimitives(epsilon, 10, q));
                fi;
            fi;
        elif n = 12 and epsilon = 1 and q < 7 then
            if q in [3, 5] then
                G := OmegaNonDegenerateImprimitives(1, 12, q, 0, 12);
                Append(maximalSubgroups, ConjugateSubgroupOmega(1, 12, q, G, 2));
            fi;
            if q <> 3 then
                Add(maximalSubgroups, OmegaNonDegenerateImprimitives(1, 12, q, -1, 6));
            fi;
            if q = 5 then
                G := OmegaNonDegenerateImprimitives(1, 12, 5, 0, 4);
                Append(maximalSubgroups, ConjugateSubgroupOmega(1, 12, 5, G, 2));
            fi;
            if q <> 2 then
                Add(maximalSubgroups, OmegaNonDegenerateImprimitives(1, 12, q, 1, 3));
            fi;
            Add(maximalSubgroups, OmegaNonDegenerateImprimitives(1, 12, q, -1, 2));
            Add(maximalSubgroups, OmegaNonDegenerateImprimitives(1, 12, q, 1, 2));
            G := OmegaIsotropicImprimitives(12, q);
            Append(maximalSubgroups, ConjugateSubgroupOmega(1, 12, q, G, 2));
        else
            Append(maximalSubgroups, C2SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
        fi;
    fi;
    
    if 3 in classes then
        # Class C3 subgroups ######################################################
        # Cf. Propositions 3.6.3 (n = 7), 3.7.5 (n = 8), 3.8.3 (n = 9), 
        # 3.9.5 (n = 10), 3.10.3 (n = 11) and 3.11.7 (n = 12) in [BHR13]
        Append(maximalSubgroups, C3SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
    fi;

    if 4 in classes then
        # Class C4 subgroups ######################################################
        # Cf. Propositions 3.7.7 (n = 8), Propositions 3.9.6 (n = 10),
        # Propositions 3.11.8 (n = 12) and Table 8.50 (n = 8) in [BHR13]
        # For all other n, class C4 is empty.
        if n = 12 and epsilon = 1 and q <> 2 then
            # number of conjugates is 2 according to [KL90] Proposition 4.4.12 (I)
            G := SymplecticTensorProductStabilizerInOmega(2, 6, q);
            Append(maximalSubgroups, ConjugateSubgroupOmega(1, 12, q, G, 2));
        elif q <> 2 and not (epsilon = 1 and n = 8) then
            Append(maximalSubgroups, C4SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
        fi;
    fi;

    if 5 in classes then
        # Class C5 subgroups ######################################################
        # Cf. Propositions 3.6.3 (n = 7), 3.7.8 (n = 8), 3.8.4 (n = 9),
        # 3.9.7 (n = 10), 3.10.3 (n = 11), 3.11.9 (n = 12) and Table 8.50 (n = 8)
        # in [BHR13]
        Append(maximalSubgroups, C5SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
    fi;

    if 6 in classes then
        # Class C6 subgroups ######################################################
        # Cf. Proposition 3.7.9 and Table 8.50 (n = 8) in [BHR13]
        # For all other n, class C6 is empty.
        if not (q - 3) mod 8 = 0 and not (q - 5) mod 8 = 0 then
            Append(maximalSubgroups, C6SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
        fi;
    fi;

    if 7 in classes then
        # Class C7 subgroups ######################################################
        # Cf. Table 8.50 (n = 8) and Proposition 3.8.3 (n = 9) in [BHR13]
        # For all other n, class C7 is empty.
        if n <> 8 then
            Append(maximalSubgroups, C7SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
        fi;
    fi;

    if 9 in classes then
        # Class C9 subgroups ######################################################
        # Cf. Theorems 4.10.18 (n = 7), 4.10.19 (n = 8), 4.10.20 (n = 9),
        #              4.10.21 (n = 10), 4.10.22 (n = 11),
        #              4.10.23 (n = 12) in [BHR13]
        # Cf. Theorems 5.11.11 (n = 7), 5.11.12 (n = 8), 5.11.13 (n = 9),
        #              5.11.14 (n = 10), 5.11.15 (n = 11),
        #              5.11.16 (n = 12) in [BHR13]
        # Cf. Tables 8.7 (n = 3), 8.17 (n = 4), 8.23 (n = 5),
        #            8.32, 8.34 (all n = 6), 8.40 (n = 7),
        #            8.50, 8.53 (all n = 8), 8.59 (n = 9),
        #            8.67, 8.69 (all n = 10), 8.75 (n = 11),
        #            8.83, 8.85 (all n = 12) in [BHR13]
        Append(maximalSubgroups, C9SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
    fi;

    return maximalSubgroups;
end);
