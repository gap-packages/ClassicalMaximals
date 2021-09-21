#
# ClassicalMaximals: Maximal subgroups of classical groups
#
# Code along the lines of:
# [1]   J. M. Bray, D. F. Holt, C. M. Roney-Dougal. "The Maximal Subgroups of the
#       Low-Dimensional Finite Classical Groups." Cambridge UP, 2013.
# [2]   D. F. Holt, C. M. Roney-Dougal. "Constructing Maximal Subgroups of
#       Classical Groups." LMS Journal of Computation and Mathematics, vol. 8,
#       2005, pp. 46-79.
# [3]   P. Kleidman, M. Liebeck. "The Subgroup Structure of the Finite
#       Classical Groups." Cambridge UP, 1990.
#
# Implementations
#

# For most classes of subgroups, we have to conjugate the subgroups we
# determined by an element C from the general group, which is not in the
# special (or quasisimple) group, in order to get representatives for all
# conjugacy classes in the special (or quasisimple) group, not only for the
# conjugacy classes in the general group (which are generally larger).
ConjugatesInGeneralGroup := function(S, C, r)
    return List([0..r - 1], i -> S ^ (C ^ i));
end;

InstallGlobalFunction(ClassicalMaximalsGeneric,
function(type, n, q, classes...)
    if Length(classes) = 0 then
        classes := [1..9];
    elif IsList(classes[1]) then
        classes := classes[1];
    fi;
    if not IsSubset([1..9], classes) then
        ErrorNoReturn("<classes> must be a subset of [1..9] but <classes> = ",
                      classes);
    fi;

    if type = "L" then
        return MaximalSubgroupClassRepsSpecialLinearGroup(n, q, classes);
    fi;
    ErrorNoReturn("not yet implemented");
end);

C1SubgroupsSpecialLinearGroupGeneric := function(n, q)
    return List([1..n-1], k -> SLStabilizerOfSubspace(n, q, k));
end;

C2SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local t, divisors, result;
    divisors := DivisorsInt(n);
    result := [];
    for t in divisors{[2..Length(divisors)]} do
        # not maximal or considered in class C_1 or C_8 by Proposition
        # 2.3.6 of [1]
        if (n > 2 and t = n and q <= 4) or (t = n / 2 and q = 2) then
            continue;  
        fi;
        Add(result, ImprimitivesMeetSL(n, q, t));
    od;
    return result;
end;

C3SubgroupsSpecialLinearGroupGeneric := function(n, q)
    return List(PrimeDivisors(n), s -> GammaLMeetSL(n, q, s));
end;

C4SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local divisorListOfn, result, n1, numberOfConjugates, generatorGLMinusSL,
    tensorProductSubgroup;
    
    divisorListOfn := List(DivisorsInt(n));
    Remove(divisorListOfn, 1);
    divisorListOfn := Filtered(divisorListOfn, x -> x < n / x);
    # Cf. Proposition 2.3.22
    if q = 2 and 2 in divisorListOfn then
        Remove(divisorListOfn, 2);
    fi;
    result := [];
    
    generatorGLMinusSL := GL(n, q).1;
    for n1 in divisorListOfn do
        tensorProductSubgroup := TensorProductStabilizerInSL(n1, QuoInt(n, n1), q);
        # Cf. Tables 3.5.A and 3.5.G in [3]
        numberOfConjugates := Gcd([q - 1, n1, QuoInt(n, n1)]);
        result := Concatenation(result,
                                ConjugatesInGeneralGroup(tensorProductSubgroup, 
                                                         generatorGLMinusSL,
                                                         numberOfConjugates));
    od;

    return result;
end;

C5SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local factorisation, p, e, generatorGLMinusSL, primeDivisorsOfe,
    degreeOfExtension, f, subfieldGroup, numberOfConjugates, result;
    
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGLMinusSL := GL(n, q).1;
    primeDivisorsOfe := PrimeDivisors(e);

    result := [];
    for degreeOfExtension in primeDivisorsOfe do
        f := QuoInt(e, degreeOfExtension);
        subfieldGroup := SubfieldSL(n, p, e, f);
        # Cf. Tables 3.5.A and 3.5.G in [3]
        numberOfConjugates := Gcd(n, QuoInt(q - 1, p ^ f - 1));
        result := Concatenation(result,
                                ConjugatesInGeneralGroup(subfieldGroup, 
                                                         generatorGLMinusSL, 
                                                         numberOfConjugates));
    od;

    return result;
end;

C6SubgroupsSpecialLinearGroupGeneric := function(n, q)
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
    generatorGLMinusSL := GL(n, q).1;

    # Cf. Table 4.6.B and the corresponding definition in [3]
    if IsOddInt(r) then
        if IsOddInt(e) and e = OrderMod(p, r) then
            extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSL(r, m, q);
            # Cf. Tables 3.5.A and 3.5.G in [3]
            numberOfConjugates := Gcd(n, q - 1);
            if n = 3 and ((q - 4) mod 9 = 0 or (q - 7) mod 9 = 0) then
                numberOfConjugates := 1;
            fi;
            result := Concatenation(result,
                                    ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                                             generatorGLMinusSL, 
                                                             numberOfConjugates)); 
        fi;
    elif m >= 2 then
        # n = 2 ^ m >= 4
        if e = 1 and (q - 1) mod 4 = 0 then
            extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSL(2, m, q);
            # Cf. Tables 3.5.A and 3.5.G in [3]
            numberOfConjugates := Gcd(n, q - 1);
            if n = 4 and (q - 5) mod 8 = 0 then
                numberOfConjugates := 2;
            fi;
            result := Concatenation(result,
                                    ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                                             generatorGLMinusSL, 
                                                             numberOfConjugates));
        fi;
    else
        # n = 2
        if e = 1 and (q - 1) mod 2 = 0 then
            extraspecialNormalizerSubgroup := ExtraspecialNormalizerInSL(2, 1, q);
            if (q - 1) mod 8 = 0 or (q - 7) mod 8 = 0 then
                # Cf. Tables 3.5.A and 3.5.G in [3]
                numberOfConjugates := Gcd(n, q - 1);
                result := Concatenation(result,
                                        ConjugatesInGeneralGroup(extraspecialNormalizerSubgroup,
                                                                 generatorGLMinusSL,
                                                                 numberOfConjugates));
            else
                Add(result, ExtraspecialNormalizerInSL(2, 1, q));
            fi;
        fi;
    fi;

    return result;
end;

C7SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local m, t, factorisationOfn, factorisationOfnExponents, highestPowern,
    result, divisorsHighestPowern, numberOfConjugates, tensorInducedSubgroup, 
    generatorGLMinusSL;

    result := [];
    generatorGLMinusSL := GL(n, q).1;
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
        tensorInducedSubgroup := TensorInducedDecompositionStabilizerInSL(m, t, q);
        # Cf. Tables 3.5.A and 3.5.G in [3]
        numberOfConjugates := Gcd(q - 1, m ^ (t - 1));
        if m mod 4 = 2 and t = 2 and q mod 4 = 3 then
            numberOfConjugates := QuoInt(numberOfConjugates, 2);
        fi;
        result := Concatenation(result, 
                                ConjugatesInGeneralGroup(tensorInducedSubgroup,
                                                         generatorGLMinusSL, 
                                                         numberOfConjugates));
    od;

    return result;
end;

C8SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local factorisation, p, e, result, generatorGLMinusSL, symplecticSubgroup,
    numberOfConjugatesSymplectic, unitarySubgroup, numberOfConjugatesUnitary,
    orthogonalSubgroup, numberOfConjugatesOrthogonal, epsilon;
    
    result := [];
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGLMinusSL := GL(n, q).1;

    if IsEvenInt(n) then
        symplecticSubgroup := SymplecticNormalizerInSL(n, q);
        # Cf. Tables 3.5.A and 3.5.G in [3]
        numberOfConjugatesSymplectic := Gcd(q - 1, QuoInt(n, 2));
        result := Concatenation(result,
                                ConjugatesInGeneralGroup(symplecticSubgroup, 
                                                         generatorGLMinusSL,
                                                         numberOfConjugatesSymplectic));
    fi;

    if IsEvenInt(e) then
        unitarySubgroup := UnitaryNormalizerInSL(n, q);
        # Cf. Tables 3.5.A and 3.5.G in [3]
        numberOfConjugatesUnitary := Gcd(p ^ QuoInt(e, 2) - 1, n);
        result := Concatenation(result,
                                ConjugatesInGeneralGroup(unitarySubgroup,
                                                         generatorGLMinusSL,
                                                         numberOfConjugatesUnitary));
    fi;

    if IsOddInt(q) then
        if IsOddInt(n) then
            orthogonalSubgroup := OrthogonalNormalizerInSL(0, n, q);
            # Cf. Tables 3.5.A and 3.5.G in [3]
            numberOfConjugatesOrthogonal := Gcd(q - 1, n);
            result := Concatenation(result,
                                    ConjugatesInGeneralGroup(orthogonalSubgroup,
                                                             generatorGLMinusSL,
                                                             numberOfConjugatesOrthogonal));
        else
            for epsilon in [1, -1] do
                orthogonalSubgroup := OrthogonalNormalizerInSL(epsilon, n, q);
                # Cf. Tables 3.5.A. and 3.5.G in [3]
                numberOfConjugatesOrthogonal := QuoInt(Gcd(q - 1, n), 2);
                result := Concatenation(result,
                                        ConjugatesInGeneralGroup(orthogonalSubgroup,
                                                                 generatorGLMinusSL,
                                                                 numberOfConjugatesOrthogonal));
            od;
        fi;
    fi;

    return result;
end;

InstallGlobalFunction(MaximalSubgroupClassRepsSpecialLinearGroup,
function(n, q, classes...)
    local maximalSubgroups, factorisation, p, e;

    if Length(classes) = 0 then
        classes := [1..9];
    elif IsList(classes[1]) then
        classes := classes[1];
    fi;
    if not IsSubset([1..9], classes) then
        ErrorNoReturn("<classes> must be a subset of [1..9] but <classes> = ",
                      classes);
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
        #                  3.10.1 (n = 11), 3.11.1 (n = 12) in [1]
        maximalSubgroups := Concatenation(maximalSubgroups,
                                          C1SubgroupsSpecialLinearGroupGeneric(n, q));
    fi;

    if 2 in classes then
        # Class C2 subgroups ######################################################
        if not n in [2, 4] then
            # Cf. Propositions 3.2.2. (n = 3), 3.4.2 (n = 5), 
            #                  3.5.2, 3.5.3, 3.5.4 all (n = 6), 3.6.2 (n = 7),
            #                  3.7.2, 3.7.3, 3.7.4 (all n = 8), 3.8.2 (n = 9),
            #                  3.9.2, 3.9.3, 3.9.4 (all n = 10), 3.10.2 (n = 11),
            #                  3.11.2, 3.11.3, 3.11.4, 3.11.5, 3.11.6 (n = 12) in [1]
            # The exceptions mentioned in these propositions are all general
            # exceptions and are dealt with directly in the function
            # C2SubgroupsSpecialLinearGeneric
            maximalSubgroups := Concatenation(maximalSubgroups,
                                              C2SubgroupsSpecialLinearGroupGeneric(n, q));
        elif n = 2 then
            # Cf. Lemma 3.1.3 and Theorem 6.3.10 in [1]
            if not q in [5, 7, 9, 11] then
                Add(maximalSubgroups, ImprimitivesMeetSL(2, q, 2));
            fi;
        else
            # n = 4

            # Cf. Proposition 3.3.2 in [1]
            if q >= 7 then
                Add(maximalSubgroups, ImprimitivesMeetSL(4, q, 4));
            fi;
            # Cf. Proposition 3.3.3 in [1]
            if q > 3 then
                Add(maximalSubgroups, ImprimitivesMeetSL(4, q, 2));
            fi;
        fi;
    fi;

    if 3 in classes then
        # Class C3 subgroups ######################################################
        # Cf. Propositions 3.3.4 (n = 4), 3.4.3 (n = 5), 3.5.5 (n = 6), 
        #                  3.6.3 (n = 7), 3.7.5 (n = 8), 3.8.3 (n = 9),
        #                  3.9.5 (n = 10), 3.10.3 (n = 11), 3.11.7 (n = 12) in [1]
        if not n in [2, 3] then
            maximalSubgroups := Concatenation(maximalSubgroups, 
                                              C3SubgroupsSpecialLinearGroupGeneric(n, q));
        elif n = 2 then
            # Cf. Lemma 3.1.4 and Theorem 6.3.10 in [1]
            if not q in [7, 9] then
                maximalSubgroups := Concatenation(maximalSubgroups, 
                                                  C3SubgroupsSpecialLinearGroupGeneric(2, q));
            fi;
        else 
            # n = 3

            # Cf. Proposition 3.2.3 in [1]
            if q <> 4 then
                maximalSubgroups := Concatenation(maximalSubgroups, 
                                                  C3SubgroupsSpecialLinearGroupGeneric(3, q));
            fi;
        fi;
    fi;

    if 4 in classes then
        # Class C4 subgroups ######################################################
        # Cf. Propositions 3.5.6 (n = 6), 3.7.7 (n = 8), 3.9.6 (n = 10), 
        #                  3.11.8 (n = 12) in [1]
        # For all other n, class C4 is empty.
        maximalSubgroups := Concatenation(maximalSubgroups,
                                          C4SubgroupsSpecialLinearGroupGeneric(n, q));
    fi;

    if 5 in classes then
        # Class C5 subgroups ######################################################
        # Cf. Propositions 3.2.4 (n = 3), 3.3.5 (n = 4), 3.4.3 (n = 5), 
        #                  3.5.7 (n = 6), 3.6.3 (n = 7), 3.7.8 (n = 8),
        #                  3.8.4 (n = 9), 3.9.7 (n = 10), 3.10.3 (n = 11),
        #                  3.11.9 (n = 12) in [1]
        if n <> 2 then
            maximalSubgroups := Concatenation(maximalSubgroups,
                                              C5SubgroupsSpecialLinearGroupGeneric(n, q));
        else
            # n = 2

            # Cf. Lemma 3.1.5 in [1]
            if  p <> 2 or not IsPrimeInt(e) then
                maximalSubgroups := Concatenation(maximalSubgroups,
                                                  C5SubgroupsSpecialLinearGroupGeneric(2, q));
            fi;
        fi;
    fi;

    if 6 in classes then
        # Class C6 subgroups ######################################################
        # Cf. Lemma 3.1.6 (n = 2) and Propositions 3.2.5 (n = 3), 3.3.6 (n = 4),
        #                                          3.4.3 (n = 5), 3.6.3 (n = 7),
        #                                          3.7.9 (n = 8), 3.8.5 (n = 9), 
        #                                          3.10.3 (n = 11) in [1]
        # For all other n, class C6 is empty.

        # Cf. Theorem 6.3.10 in [1]
        if n <> 2 or not q mod 40 in [11, 19, 21, 29] then 
            maximalSubgroups := Concatenation(maximalSubgroups,
                                              C6SubgroupsSpecialLinearGroupGeneric(n, q));
        fi;
    fi;

    if 7 in classes then
        # Class C7 subgroups ######################################################
        # Cf. Proposition 3.8.6 (n = 9) in [1]
        # For all other n, class C7 is empty.
        maximalSubgroups := Concatenation(maximalSubgroups,
                                          C7SubgroupsSpecialLinearGroupGeneric(n, q));
    fi;

    if 8 in classes then
        # Class C8 subgroups ######################################################
        # Cf. Lemma 3.1.1 (n = 2) and Propositions 3.2.6 (n = 3), 3.3.7 (n = 4),
        #                                          3.4.3 (n = 5), 3.5.8 (n = 6),
        #                                          3.6.3 (n = 7), 3.7.11 (n = 8),
        #                                          3.8.7 (n = 9), 3.9.8 (n = 10),
        #                                          3.10.3 (n = 11), 3.11.10 (n = 12) in [1]
        if n <> 2 then
            maximalSubgroups := Concatenation(maximalSubgroups,
                                              C8SubgroupsSpecialLinearGroupGeneric(n, q));
        fi;
    fi;

    return maximalSubgroups;
end);
