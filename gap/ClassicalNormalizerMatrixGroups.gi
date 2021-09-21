# Construction as in Proposition 11.1 of [2]
BindGlobal("SymplecticNormalizerInSL",
function(d, q)
    local zeta, gcd, A, B, C, D, i, E, result;
    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even but <d> = ", d);
    fi;

    zeta := PrimitiveElement(GF(q));
    A := Sp(d, q).1;
    B := Sp(d, q).2;
    gcd := Gcd(d, q - 1);
    # generates the center of SL(d, q)
    C := zeta ^ QuoInt(q - 1, gcd) * IdentityMat(d, GF(q));

    if IsEvenInt(q) or gcd / 2 = Gcd(q - 1, d / 2) then
        result := Group([A, B, C]);
        # Size according to Table in [1]
        SetSize(result, gcd * Size(PSp(d, q)));
    else
        D := DiagonalMat(Concatenation(List([1..d / 2], i -> zeta),
                                       List([1..d / 2], i -> zeta ^ 0)));
        # solving the congruence d * i = d / 2 mod q - 1 for i
        i := (d / 2) / gcd * (d / gcd) ^ (-1) mod ((q - 1) / gcd);
        E := zeta ^ (-i) * D;
        result := Group([A, B, C, E]);
        # Size according to Table 2.11 in [1]
        # Note that |PCSp(d, q)| = |CSp(d, q)| / (q - 1) 
        #                        = |Sp(d, q)| * |CSp(d, q) : Sp(d, q)| / (q - 1) 
        #                        = |Sp(d, q)|,
        # since |CSp(d, q) : Sp(d, q)| = q - 1 according to Table 1.3 of [1]
        SetSize(result, gcd * Size(Sp(d, q)));
    fi;

    return result;
end);

# Construction as in Proposition 11.3 of [2]
BindGlobal("UnitaryNormalizerInSL",
function(d, q)
    local qFactorization, e, p, q0, zeta, C, g, c, SUWithIdentityForm, SUGens, gens, D, zetaId, solution, result;
    qFactorization := PrimePowersInt(q);
    e := qFactorization[2];
    if IsOddInt(e) then
        ErrorNoReturn("No such subrgoups exist since <q> is not square.");
    fi;
    p := qFactorization[1];

    q0 := p^(QuoInt(e, 2));
    zeta := PrimitiveElement(GF(q));
    C := zeta^(QuoInt((q - 1), Gcd(q - 1, d))) * IdentityMat(d, GF(q)); # generates the center of SL(d, q)
    g := Gcd(q - 1, d);
    c := QuoInt(Gcd(q0 + 1, d) * (q - 1), Lcm(q0 + 1, QuoInt(q - 1, g)) * g);
    SUWithIdentityForm := ChangeFixedSesquilinearForm(SU(d, q0), IdentityMatrix(GF(q0), d));
    SUGens := GeneratorsOfGroup(SUWithIdentityForm);

    gens := Concatenation(SUGens, [C]);
    if not IsOne(c) then
        D := (GL(d, q).1) ^ (q0 - 1); # diagonal matrix [zeta^(q0 - 1), 1, ..., 1]
        zetaId := zeta * IdentityMat(d, GF(q));
        for solution in NullspaceIntMat([[q0 - 1], [d], [q - 1]]) do
            Add(gens, D ^ solution[1] * zetaId ^ solution[2]);
        od;
    fi;

    result := Group(gens);
    # Size according to Table 2.11 in [1]
    SetSize(result, Size(SUWithIdentityForm) * Gcd(q0 - 1, d));
    return result;
end);

ReflectionMatrix := function(n, q, gramMatrix, v)
    local reflectionMatrix, i, basisVector, reflectBasisVector, beta;
    reflectionMatrix := NullMat(n, n, GF(q));
    beta := BilinearFormByMatrix(gramMatrix);
    for i in [1..n] do
        basisVector := List([1..n], j -> 0 * Z(q));
        basisVector[i] := Z(q) ^ 0;
        reflectBasisVector := basisVector 
                              - 2 * EvaluateForm(beta, v, basisVector) 
                              / EvaluateForm(beta, v, v) * v;
        reflectionMatrix[i]{[1..n]} := reflectBasisVector;
    od;
    return reflectionMatrix;
end;

# Construct generators for the orthogonal groups with the properties listed in
# Lemma 2.4 of [2].
# Construction as in: C. M. Roney-Dougal. "Conjugacy of Subgroups of the
# General Linear Group." Experimental Mathematics, vol. 13 no. 2, 2004, pp.
# 151-163. Lemma 2.4.
# We take the notation from [2].
GeneratorsOfOrthogonalGroup := function(epsilon, n, q)
    local gramMatrix, generatorsOfSO, vectorOfSquareNorm, D, E, zeta, a, b,
    solutionOfQuadraticCongruence;
    if IsEvenInt(q) then
        ErrorNoReturn("This function was only designed for <q> odd but <n> = ", 
                      n, "and <q> = ", q);
    fi;

    zeta := PrimitiveElement(GF(q));
    if IsOddInt(n) then
            gramMatrix := IdentityMat(n, GF(q));
            generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                            gramMatrix));
            D := - IdentityMat(n, GF(q));
            E := zeta * IdentityMat(n, GF(q));
    else 
        if epsilon = 1 then
            gramMatrix := AntidiagonalMat(List([1..n], i -> One(GF(q))), GF(q));
            generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                            gramMatrix));
            # Our standard bilinear form is given by the Gram matrix 
            # Antidiag(1, ..., 1). The norm of [1, 0, ..., 0, 2] under this
            # bilinear form is 4, i.e. a square. (Recall q odd, so this is not zero!)
            vectorOfSquareNorm := zeta ^ 0 * Concatenation([1], 
                                                           List([1..n - 2], i -> 0), 
                                                           [2]);
            D := ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
            E := DiagonalMat(Concatenation(List([1..n / 2], i -> zeta), 
                                           List([1..n / 2], i -> 1)));
        elif epsilon = -1 then

            # Get a, b in GF(q) with a ^ 2 + b ^ 2 = zeta
            solutionOfQuadraticCongruence := SolveQuadraticCongruence(zeta, q);
            a := solutionOfQuadraticCongruence.a;
            b := solutionOfQuadraticCongruence.b;

            if IsOddInt(n * (q - 1) / 4) then
                gramMatrix := IdentityMat(n, GF(q));
                generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                                gramMatrix));
                # Our standard bilinear form is given by the Gram matrix 
                # Diag(1, ..., 1). The norm of [1, 0, ..., 0] under this bilinear
                # form is 1, i.e. a square.
                vectorOfSquareNorm := zeta ^ 0 * Concatenation([1], 
                                                               List([1..n - 1], i -> 0));
                D := ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
                # Block diagonal matrix consisting of n / 2 blocks of the form 
                # [[a, b], [b, -a]].
                E := MatrixByEntries(GF(q), n, n, 
                                     Concatenation(List([1..n], i -> [i, i, (-1) ^ (i + 1) * a]), 
                                                   List([1..n], i -> [i, i + (-1) ^ (i + 1), b])));
            else
                gramMatrix := Z(q) ^ 0 * DiagonalMat(Concatenation([zeta],
                                                                   List([1..n - 1], i -> 1)));
                generatorsOfSO := GeneratorsOfGroup(ChangeFixedSesquilinearForm(SO(epsilon, n, q),
                                                                                gramMatrix));
                # Our standard bilinear form is given by the Gram matrix 
                # Diag(zeta, 1, ..., 1). The norm of [0, ..., 0, 1] under this
                # bilinear form is 1, i.e. a square.
                vectorOfSquareNorm := zeta ^ 0 * Concatenation(List([1..n - 1], i -> 0), 
                                                               [1]);
                D := ReflectionMatrix(n, q, gramMatrix, vectorOfSquareNorm);
                # Block diagonal matrix consisting of one block [[0, zeta], [1, 0]]
                # and n / 2 - 1 blocks of the form [[a, b], [b, -a]].
                E := MatrixByEntries(GF(q), n, n, 
                                     Concatenation([[1, 2, zeta], [2, 1, zeta ^ 0]],
                                                   List([3..n], i -> [i, i, (-1) ^ (i + 1) * a]), 
                                                   List([3..n], i -> [i, i + (-1) ^ (i + 1), b])));
            fi;
        fi;
    fi;
    
    return rec(generatorsOfSO := generatorsOfSO, D := D, E := E);
end;

# Construction as in Proposition 11.2 of [2]
# Note, though, that the construction of the matrix W as in Proposition 8.4 of
# [2] does not lead to correct results here - we provide our own construction
# here instead.
BindGlobal("OrthogonalNormalizerInSL",
function(epsilon, d, q)
    local generatingScalar, zeta, generatorsOfOrthogonalGroup, generators,
    result, i1, DEpsilon, EEpsilon, X, W, i2, k;
    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be an odd integer but <q> = ", q);
    fi;
    if d <= 2 then
        ErrorNoReturn("This function might not work with <d> <= 2 but <d> = ", d);
    fi;

    zeta := PrimitiveElement(GF(q));
    generatingScalar := zeta ^ QuoInt(q - 1, Gcd(q - 1, d)) * IdentityMat(d, GF(q));
    generatorsOfOrthogonalGroup := GeneratorsOfOrthogonalGroup(epsilon, d, q);
    # These are A_epsilon, B_epsilon and C in [2]
    generators := Concatenation(generatorsOfOrthogonalGroup.generatorsOfSO,
                                [generatingScalar]);
    
    # We now construct an element W of determinant 1 in 
    # SL(d, q) - Z(SL(d, q)).SO(d, q) which has order 2 modulo 
    # Z(SL(d, q)).SO(d, q) following Proposition 8.4 of [2]
    if IsEvenInt(d) then
        # det(DEpsilon) = -1
        DEpsilon := generatorsOfOrthogonalGroup.D;
        # det(EEpsilon) = (epsilon * omega) ^ (d / 2)
        EEpsilon := generatorsOfOrthogonalGroup.E;
        X := zeta * IdentityMat(d, GF(q));
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

    result := Group(generators);
    # Size according to Table 2.11 in [1] (note that the structure given in
    # Proposition 11.2 of [2] is wrong!)
    SetSize(result, Gcd(q - 1, d) * Size(SO(epsilon, d, q)));
    return result;
end);
