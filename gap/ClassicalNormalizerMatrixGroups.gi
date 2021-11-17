# Construction as in Proposition 11.1 of [HR05]
BindGlobal("SymplecticNormalizerInSL",
function(d, q)
    local F, zeta, gcd, AandB, C, D, i, E, size, generators, standardForm;
    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even but <d> = ", d);
    fi;

    F := GF(q);
    zeta := PrimitiveElement(F);
    standardForm := AntidiagonalMat(Concatenation(List([1..d / 2], i -> - zeta ^ 0),
                                                  List([1..d / 2], i -> zeta ^ 0)), 
                                    F);

    AandB := ShallowCopy(GeneratorsOfGroup(ConjugateToSesquilinearForm(Sp(d, q), 
                                                                       "S", 
                                                                       standardForm)));
    gcd := Gcd(d, q - 1);
    # generates the center of SL(d, q)
    C := zeta ^ QuoInt(q - 1, gcd) * IdentityMat(d, F);
    generators := Concatenation(AandB, [C]);

    if IsEvenInt(q) or gcd / 2 = Gcd(q - 1, d / 2) then
        # Size according to Table 2.11 in [BHR13]
        size := gcd * SizePSp(d, q);
    else
        D := DiagonalMat(Concatenation(List([1..d / 2], i -> zeta),
                                       List([1..d / 2], i -> zeta ^ 0)));
        # solving the congruence d * i = d / 2 mod q - 1 for i
        i := (d / 2) / gcd * (d / gcd) ^ (-1) mod ((q - 1) / gcd);
        E := zeta ^ (-i) * D;
        # Size according to Table 2.11 in [BHR13]
        # Note that |PCSp(d, q)| = |CSp(d, q)| / (q - 1) 
        #                        = |Sp(d, q)| * |CSp(d, q) : Sp(d, q)| / (q - 1) 
        #                        = |Sp(d, q)|,
        # since |CSp(d, q) : Sp(d, q)| = q - 1 according to Table 1.3 of [BHR13]
        size := gcd * SizeSp(d, q);
        Add(generators, E);
    fi;

    return MatrixGroupWithSize(F, generators, size);
end);

# Construction as in Proposition 11.3 of [HR05]
BindGlobal("UnitaryNormalizerInSL",
function(d, q)
    local F, qFactorization, e, p, q0, zeta, C, g, c, SUWithIdentityForm, 
        SUGens, gens, D, zetaId, solution, size;
    qFactorization := PrimePowersInt(q);
    e := qFactorization[2];
    if IsOddInt(e) then
        ErrorNoReturn("No such subrgoups exist since <q> is not square.");
    fi;
    p := qFactorization[1];

    F := GF(q);
    q0 := p^(QuoInt(e, 2));
    zeta := PrimitiveElement(F);
    C := zeta^(QuoInt((q - 1), Gcd(q - 1, d))) * IdentityMat(d, F); # generates the center of SL(d, q)
    g := Gcd(q - 1, d);
    c := QuoInt(Gcd(q0 + 1, d) * (q - 1), Lcm(q0 + 1, QuoInt(q - 1, g)) * g);
    SUWithIdentityForm := ConjugateToSesquilinearForm(SU(d, q0), "U", IdentityMatrix(GF(q0), d));
    SUGens := GeneratorsOfGroup(SUWithIdentityForm);

    gens := Concatenation(SUGens, [C]);
    if not IsOne(c) then
        D := GLMinusSL(d, q) ^ (q0 - 1); # diagonal matrix [zeta^(q0 - 1), 1, ..., 1]
        zetaId := zeta * IdentityMat(d, F);
        for solution in NullspaceIntMat([[q0 - 1], [d], [q - 1]]) do
            Add(gens, D ^ solution[1] * zetaId ^ solution[2]);
        od;
    fi;

    # Size according to Table 2.11 in [BHR13]
    size := SizeSU(d, q0) * Gcd(q0 - 1, d);
    return MatrixGroupWithSize(F, gens, size);
end);

# Construction as in Proposition 11.2 of [HR05]
# Note, though, that the construction of the matrix W as in Proposition 8.4 of
# [HR05] does not lead to correct results here - we provide our own construction
# here instead.
BindGlobal("OrthogonalNormalizerInSL",
function(epsilon, d, q)
    local F, generatingScalar, zeta, generatorsOfOrthogonalGroup, generators,
    i1, DEpsilon, EEpsilon, X, W, i2, k, size;
    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be an odd integer but <q> = ", q);
    fi;
    if d <= 2 then
        ErrorNoReturn("This function might not work with <d> <= 2 but <d> = ", d);
    fi;
    
    F := GF(q);
    zeta := PrimitiveElement(F);
    generatingScalar := zeta ^ QuoInt(q - 1, Gcd(q - 1, d)) * IdentityMat(d, F);
    generatorsOfOrthogonalGroup := GeneratorsOfOrthogonalGroup(epsilon, d, q);
    # These are A_epsilon, B_epsilon and C in [HR05]
    generators := Concatenation(generatorsOfOrthogonalGroup.generatorsOfSO,
                                [generatingScalar]);
    
    # We now construct an element W of determinant 1 in 
    # SL(d, q) - Z(SL(d, q)).SO(d, q) which has order 2 modulo 
    # Z(SL(d, q)).SO(d, q) following Proposition 8.4 of [HR05]
    if IsEvenInt(d) then
        # det(DEpsilon) = -1
        DEpsilon := generatorsOfOrthogonalGroup.D;
        # det(EEpsilon) = (epsilon * omega) ^ (d / 2)
        EEpsilon := generatorsOfOrthogonalGroup.E;
        X := zeta * IdentityMat(d, F);
        k := Gcd(q - 1, d);

        # We deal with the cases epsilon = +1 and epsilon = -1 simultaneously
        if IsEvenInt((q - 1) / k) then
            i1 := QuoInt(q - 1, 2 * k);
            # Note that det(X ^ i1) = zeta ^ (d * (q - 1) / 2 * k) 
            #                       = zeta ^ (Lcm(d, q - 1) / 2)
            #                       = -1
            # since the 2-adic valuation of q - 1 is greater than the 2-adic
            # valuation of d, hence det(W) = 1. Obviously, W ^ 2 is in 
            # Z(SL(d, q)).SO(d, q). Suppose W were already in that group; then
            # there is a scalar S with S * W in SO(d, q) implying
            # S * X ^ i1 * DEpsilon * gramMatrix * DEpsilon ^ T * X ^ i1 * S 
            # = gramMatrix - but the LHS is (S * X ^ i1) ^ 2 * gramMatrix,
            # which means S = +- X ^ (-i1), which is not in SL - contradiction. 
            W := X ^ i1 * DEpsilon;
        else 
            i2 := ((q - 1) / k - 1) / 2; # an integer since (q - 1) / k is odd
            if IsEvenInt(d / k) or (epsilon = -1 and IsOddInt(d / 2)) then
                # Note that det(X ^ i2) = zeta ^ (d * ((q - 1) / k - 1) / 2)
                #                       = zeta ^ (d * (q - 1)) / (2 * k) * zeta ^ (- d / 2)
                #                       = zeta ^ (Lcm(d, q - 1) / 2) * zeta ^ (- d / 2).
                # If d / k is even, the 2-adic valuation of d is greater than
                # the 2-adic valuation of q - 1, hence det(X ^ i2) = zeta ^ (- d / 2).
                # Otherwise, the two valuations are the same (since (q - 1) / k
                # is odd) and we have det(X ^ i2) = - zeta ^ (- d / 2). Since
                # we have det(EEpsilon) = zeta ^ (d / 2) in the former case an
                # det(EEpsilon) = - zeta ^ (d / 2) in the latter, we have in
                # each case det(W) = 1. W ^ 2 is in Z(SL(d, q)).SO(d, q) since
                # W ^ 2 = X ^ (2 * i2) * EEpsilon ^ 2 
                #       = (zeta * X ^ (2 * i2)) * (1 / zeta * EEpsilon ^ 2)
                # and the first factor is in Z(SL(d, q)) while the second in in
                # SO(d, q). Suppose W were already in Z(SL(d, q)).SO(d, q); then 
                # there is a scalar S with S * W in SO(d, q) implying
                # S * X ^ i2 * EEpsilon * gramMatrix * EEpsilon ^ T * X ^ i2 * S
                # = gramMatrix - but the LHS is 
                # zeta * (S * X ^ i2) ^ 2 * gramMatrix, which means we must
                # have zeta * (S * X ^ i2) ^ 2 = IdentityMat - contradiction
                # since zeta is not a square in GF(q). 
                W := X ^ i2 * EEpsilon;
            else
                # As above, we get det(X ^ i2) = - zeta ^ (- d / 2). Since
                # det(EEpsilon) = zeta ^ (d / 2) and det(DEpsilon) = -1, we
                # have det(W) = 1. Similar arguments to the previous case show
                # that W ^ 2 is in Z(SL(d, q)).SO(d, q) but W is not.
                W := X ^ i2 * EEpsilon * DEpsilon;
            fi;
        fi;

        Add(generators, W);
    fi;

    # Size according to Table 2.11 in [1] (note that the structure given in
    # Proposition 11.2 of [HR05] is wrong!)
    size := Gcd(q - 1, d) * SizeSO(epsilon, d, q);
    return MatrixGroupWithSize(F, generators, size);
end);
