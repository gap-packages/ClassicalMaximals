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
    fi;
    ErrorNoReturn("not yet implemented");
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
    local m, result, listOfks;

    m := QuoInt(n, 2);
    result := [];

    # Isotropic type, number of conjugates according to Proposition 4.1.20 (I) in [KL90]
    if epsilon = -1 then
        listOfks := [1..m - 1];
    elif epsilon = 0 then
        listOfks := [1..m];
    elif epsilon = 1 then
        listOfks := [1..m - 2];
        Add(listOfks, m);
        Append(result, ConjugateSubgroupOmega(epsilon, n, q, OmegaStabilizerOfIsotropicSubspace(epsilon, n, q, m - 1), 2));
    fi;
    Append(result, List(listOfks, k -> OmegaStabilizerOfIsotropicSubspace(epsilon, n, q, k)));

    # Non-degenerate type, number of conjugates according to Proposition 4.1.6 (I) in [KL90]
    if epsilon = 0 then

        listOfks := 2 * [1..m] - 1;
        Append(result, List(listOfks, k -> OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, -1, k)));

        # Cf. Proposition 2.3.2 (iii) in [BHR13]
        if q in [2, 3] then
            Remove(listOfks, 1);
        fi;
        Append(result, List(listOfks, k -> OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, 1, k)));

    else

        if IsOddInt(q) then
            listOfks := 2 * [1..QuoInt(m, 2)] - 1;
            Append(result, Flat(List(listOfks, k -> ConjugateSubgroupOmega(epsilon, n, q, OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, 0, k), 2))));
        fi;

        if epsilon = -1 then
            listOfks := 2 * [1..QuoInt(m, 2)];
        else
            listOfks := 2 * [1..QuoInt(m - 1, 2)];
        fi;
        Append(result, List(listOfks, k -> OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, -1, k)));

        # Cf. Proposition 2.3.2 (iii) in [BHR13]
        if q = 2 then
            Remove(listOfks, 1);
        fi;
        Append(result, List(listOfks, k -> OmegaStabilizerOfNonDegenerateSubspace(epsilon, n, q, 1, k)));

    fi;

    # Non-singular type, number of conjugates according to Proposition 4.1.7 (I) in [KL90]
    if IsEvenInt(q) then
        Add(result, OmegaStabilizerOfNonSingularVector(epsilon, n, q));
    fi;

    return result;

BindGlobal("C5SubgroupsOrthogonalGroupGeneric",
function(epsilon, n, q)
    local factorisationOfq, p, e, listOfrs, result,
    numberOfConjugatesPlus, numberOfConjugatesMinus, r;

    factorisationOfq := PrimePowersInt(q);
    p := factorisationOfq[1];
    e := factorisationOfq[2];

    listOfrs := List(PrimeDivisors(e));
    result := [];

    if epsilon = 0 then

        # number of conjugates according to [KL90] Proposition 4.5.8 (I)
        if 2 in listOfrs then
            Append(result, ConjugateSubgroupOmega(epsilon, n, q, SubfieldOmega(0, n, p, e, QuoInt(e, 2), 0), 2));
            Remove(listOfrs, 1);
        fi;

    else

        if 2 in listOfrs then

            # number of conjugates according to [KL90] Proposition 4.5.10 (I)
            if epsilon = 1 then
                if IsEvenInt(q) then
                    numberOfConjugatesPlus := 1;
                    numberOfConjugatesMinus := 1;
                else
                    if n mod 4 = 2 and p ^ QuoInt(e, 2) mod 4 = 1 then
                        numberOfConjugatesPlus := 2;
                        numberOfConjugatesMinus := 4;
                    else
                        numberOfConjugatesPlus := 4;
                        numberOfConjugatesMinus := 2;
                    fi;
                fi;
                Append(result, ConjugateSubgroupOmega(epsilon, n, q, SubfieldOmega(1, n, p, e, QuoInt(e, 2), 1), numberOfConjugatesPlus));
                Append(result, ConjugateSubgroupOmega(epsilon, n, q, SubfieldOmega(1, n, p, e, QuoInt(e, 2), -1), numberOfConjugatesMinus));
            fi;
            Remove(listOfrs, 1);

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

InstallGlobalFunction(MaximalSubgroupClassRepsOrthogonalGroup,
function(epsilon, n, q, classes...)
    local maximalSubgroups;

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
        # Class C6 subgroups ######################################################
        # Cf. Propositions 3.6.1 (n = 7), 3.7.1 (n = 8), 3.8.1 (n = 9),
        # 3.9.1 (n = 10), 3.10.1 (n = 11), 3.11.1 (n = 12)
        # and Table 8.50 (n = 8) in [BHR13]
        Append(maximalSubgroups, C1SubgroupsOrthogonalGroupGeneric(epsilon, n, q));

    if 5 in classes then
        # Class C5 subgroups ######################################################
        # Cf. Propositions 3.6.3 (n = 7), 3.7.8 (n = 8), 3.8.4 (n = 9),
        # 3.9.7 (n = 10), 3.10.3 (n = 11), 3.11.9 (n = 12) and Table 8.50 (n = 8)
        # in [BHR13]
        Append(maximalSubgroups, C5SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
    fi;

    if 6 in classes then
        # Class C6 subgroups ######################################################
        # Cf. Propositions 3.7.9 and Table 8.50 (n = 8) in [BHR13]
        # For all other n, class C6 is empty.
        if not (q - 3) mod 8 = 0 and not (q - 5) mod 8 = 0 then
            Append(maximalSubgroups, C6SubgroupsOrthogonalGroupGeneric(epsilon, n, q));
        fi;
    fi;

    return maximalSubgroups;
end);
