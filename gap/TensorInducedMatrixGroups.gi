######################## WORKING OUT FOR ELSE BRANCH BELOW ####################
#
#     Let m be even and assume that a generator of the
#     TensorWreathProduct(SL(m, q), Sym(t)) (or the same with SU(m, q) instead
#     of SL(m, q), respectively) has determinant not equal to 1.
#
#     We generate TensorWreathProduct(SL(m, q), Sym(t)) from 
#       * (t - 1)-fold Kronecker products of the generators of SL(m, q) with 
#         mxm identity matrices 
#       * permutation matrices constructed in the following way: the group
#         Sym(t) acts naturally on the set Omega of t-tuples over [1..m] giving
#         a homomorphism psi : Sym(t) --> Sym(m ^ t); we take the permutation
#         matrices associated to the images of the generators of Sym(t) under
#         the homomorphism psi
#     The first class of generators obviously always has determinant 1, the
#     second class has determinant +-1. We take (1, 2) and (1, 2, 3, ..., t) as
#     generators of Sym(t).
#
#     psi((1, 2)) is a product of m * (m - 1) / 2 * m ^ (t - 2) cycles of length 2 
#     (for any two different a1, a2 in [1..m] and any a3, ..., at in [1..m] the 
#     tuples [a1, a2, ..., at] and [a2, a1, ..., at] are swapped). Therefore 
#     det(PermutationMat(phi((1, 2)))) = sign(psi((1, 2))) 
#                                      = (-1) ^ ((m * (m - 1)) / 2 * m ^ (t - 2)) 
#     For m even, this is -1 if and only if m = 2 mod 4 and t = 2.
#
#     Let A_d be the number of t-tuples from [1..m] that can be divided into d
#     equal blocks. Then A_d = m ^ (t / d) if d | t and 0 otherwise. Now let B_e 
#     be the number of t-tuples from [1..m] that can be divided into e and not 
#     more equal blocks. We have A_d = sum_{d | e} B_e for d | t. Hence
#
#               m ^ (t / d) = sum_{d | e} B_e.
#
#     Swap d and t / d as well as e and t / e, obtain
#
#               m ^ d = sum_{t / d | t / e} B_{t / e} = sum_{e | d} B_{t / e}.
#
#     Applying the Mobius inversion formula
#
#               B_{t / d} = sum_{e | d} mu(d / e) * m ^ e = 0 mod 2
#
#     since m is even for all d (this can also be seen without the Mobius
#     inversion formula by induction). But decomposing psi((1, 2, ..., t)) into
#     a product of cycles gives exactly B_{t / d} cycles of length d. Therefore
#     det(PermutationMat(phi((1, 2, ..., t)))) = sign(psi((1, 2, ..., t)))
#                                              = 1.
#
#     Conclusion: If m is even and we have a generator of determinant -1, then
#     t = 2 and m = 2 mod 4. It then follows that in the else branch below, we
#     must have q = 1 mod 4: The case t = 2, m = 2 mod 4 and q = 3 mod 4 was
#     filtered out in an if-statement before and the case q even will always
#     give determinant 1 as -1 = 1 in characteristic 2.
#
#     In the unitary case, the analysis above still holds true; however, now
#     the case t = 2, m = 2 mod 4 and q = 1 mod 4 was filtered out before so 
#     t = 2, m = 2 mod 4 and q = 3 mod 4 remains.
#
###############################################################################     


# Construction as in Proposition 10.2 of [HR05]
BindGlobal("TensorInducedDecompositionStabilizerInSL",
function(m, t, q)
    local F, gensOfSLm, I, D, C, generatorsOfHInSL, i, H, E, U, S, zeta, mu,
    size, scalingMatrix, d, generator;
    if not t > 1 or not m > 1 then
        ErrorNoReturn("<t> must be greater than 1 and <m> must be greater than 1");
    fi;

    F := GF(q);
    d := m ^ t;
    zeta := PrimitiveElement(F);
    D := DiagonalMat(Concatenation([zeta], List([1..m - 1], i -> zeta ^ 0)));
    C := zeta ^ ((q - 1) / Gcd(q - 1, d)) * IdentityMat(d, F);

    if t = 2 and m mod 4 = 2 and q mod 4 = 3 then
        gensOfSLm := GeneratorsOfGroup(SL(m, q));
        I := IdentityMat(m, F);
        # Let Z = Z(SL(d, q)). Then these generate the group 
        # Z.(SL(m, q) o SL(m, q)) (to see this, realize the first factor of the
        # central product as all Kronecker Products I * M with M in SL(m, q)
        # and, similarly, the second factor as the Kronecker Products M * I).
        generatorsOfHInSL := [KroneckerProduct(gensOfSLm[1], I),
                              KroneckerProduct(gensOfSLm[2], I),
                              KroneckerProduct(I, gensOfSLm[1]),
                              KroneckerProduct(I, gensOfSLm[2])];
    else
        H := TensorWreathProduct(SL(m, q), SymmetricGroup(t));
        generatorsOfHInSL := [];
        for generator in GeneratorsOfGroup(H) do
            if DeterminantMat(generator) = zeta ^ 0 then
                Add(generatorsOfHInSL, generator);
            else
                # det = -1 for odd permutation
                if IsOddInt(m) then
                    Add(generatorsOfHInSL, -1 * generator);
                else
                    # In this case, we have t = 2, m = 2 mod 4 and q = 1 mod 4
                    # (see working out above).

                    # This has determinant ((det D) ^ ((q - 1) / 4)) ^ m 
                    # = (zeta ^ ((q - 1) / 4)) ^ m, which, using m even,
                    # becomes (zeta ^ ((q - 1) / 2)) ^ (m / 2) = (-1) ^ (m / 2)
                    # and this is -1 due to m = 2 mod 4.
                    scalingMatrix := KroneckerProduct(D ^ QuoInt(q - 1, 4), 
                                                      IdentityMat(m, F));
                    # det(generator * scalingMatrix) = -1 * (-1) = 1
                    Add(generatorsOfHInSL,(generator * scalingMatrix));
                fi;
            fi;
        od;
    fi;

    U := KroneckerProduct(D, D ^ (-1));
    for i in [3..t] do
        U := KroneckerProduct(U, IdentityMat(m, F));
    od;
    # det(U) = 1
    E := D ^ QuoInt(Gcd(q - 1, d), Gcd(q - 1, m ^ (t - 1)));
    for i in [2..t] do
        E := KroneckerProduct(E, IdentityMat(m, F));
    od;
    # det(E) = zeta ^ (Gcd(q - 1, d) / Gcd(q - 1, m ^ (t - 1)) * m ^ (t - 1))
    #        = zeta ^ (Gcd(q - 1, d) / Gcd(q - 1, m ^ (t - 1)) * d / m)

    # Write mu = zeta ^ k for some k. We want 
    # zeta ^ Gcd(q - 1, d) = det(mu * I_d) = mu ^ d = zeta ^ (kd), thus 
    # kd = Gcd(q - 1, d) mod (q - 1). Dividing through by Gcd(q - 1, d) gives 
    # k * d / Gcd(q - 1, d) = 1 mod ((q - 1) / Gcd(q - 1, d)) and now 
    # d / Gcd(q - 1, d) is invertible leading to 
    # k = 1 / (d / Gcd(q - 1, d)) mod ((q - 1) / Gcd(q - 1, d)).
    mu := zeta ^ (1 / (d / Gcd(q - 1, d)) mod ((q - 1) / Gcd(q - 1, d)));
    S := mu ^ (- d / (Gcd(q - 1, d / m) * m)) * IdentityMat(d, F);
    # det(S) = det(mu * I_d) ^ (- d / (Gcd(q - 1, d / m) * m))
    #        = (zeta ^ Gcd(q - 1, d)) ^ (- d / (Gcd(q - 1, d / m) * m))
    #        = zeta ^ (- Gcd(q - 1, d) / Gcd(q - 1, m ^ (t - 1)) * d / m)
    #        = det(E) ^ (-1)

    # Size according to Table 2.10 of [BHR13]
    if t = 2 and m mod 4 = 2 and q mod 4 = 3 then
        size := Gcd(q - 1, m) * SizePSL(m, q) ^ 2 * Gcd(q - 1, m) ^ 2;
    else
        size := Gcd(q - 1, m) * SizePSL(m, q) ^ t 
                              * Gcd(q - 1, m ^ (t - 1)) * Gcd(q - 1, m) ^ (t - 1) 
                              * Factorial(t);
    fi;
    return MatrixGroupWithSize(F, Concatenation(generatorsOfHInSL, [C, U, S * E]), size);
end);

# Construction as in Proposition 10.4 of [HR05]
# Note, though, that the structure of G / Z(G) given there is incorrect and
# that one should rather consult Table 2.10 of [BHR13] on that (which, however, 
# gives the structure of G, not G / Z(G)!).
BindGlobal("TensorInducedDecompositionStabilizerInSU",
function(m, t, q)
    local F, gensOfSUm, I, D, C, generatorsOfHInSU, i, H, E, U, S, zeta, mu,
    size, scalingMatrix, d, generator, k, result;
    if not t > 1 or not m > 1 then
        ErrorNoReturn("<t> must be greater than 1 and <m> must be greater than 1");
    fi;

    F := GF(q ^ 2);
    d := m ^ t;
    zeta := PrimitiveElement(F);
    D := DiagonalMat(Concatenation([zeta], 
                                   List([1..m - 2], i -> zeta ^ 0),
                                   [zeta ^ (- q)]));
    # generates the center of SU(d, q)
    C := zeta ^ ((q ^ 2 - 1) / Gcd(q + 1, d)) * IdentityMat(d, F);

    if t = 2 and m mod 4 = 2 and q mod 4 = 1 then
        gensOfSUm := GeneratorsOfGroup(SU(m, q));
        I := IdentityMat(m, F);
        # Let Z = Z(SU(d, q)). Then these generate the group 
        # Z.(SU(m, q) o SU(m, q)) (to see this, realize the first factor of the
        # central product as all Kronecker Products I * M with M in SU(m, q)
        # and, similarly, the second factor as the Kronecker Products M * I).
        generatorsOfHInSU := [KroneckerProduct(gensOfSUm[1], I),
                              KroneckerProduct(gensOfSUm[2], I),
                              KroneckerProduct(I, gensOfSUm[1]),
                              KroneckerProduct(I, gensOfSUm[2])];
    else
        H := TensorWreathProduct(ConjugateToSesquilinearForm(SU(m, q),
                                                             "U",
                                                             AntidiagonalMat(m, F),
                                                             F), 
                                 SymmetricGroup(t));
        generatorsOfHInSU := [];
        for generator in GeneratorsOfGroup(H) do
            if DeterminantMat(generator) = zeta ^ 0 then
                Add(generatorsOfHInSU, generator);
            else
                # det = -1 for odd permutation
                if IsOddInt(m) then
                    Add(generatorsOfHInSU, -1 * generator);
                else
                    # In this case, we have t = 2, m = 2 mod 4 and q = 3 mod 4
                    # (see working out above).

                    # This has determinant ((det D) ^ ((q + 1) / 4)) ^ m 
                    # = ((zeta ^ (1 - q)) ^ ((q + 1) / 4)) ^ m, which, using m even,
                    # becomes (zeta ^ (- (q ^ 2 - 1) / 2)) ^ (m / 2) = (-1) ^ (m / 2)
                    # and this is -1 due to m = 2 mod 4.
                    scalingMatrix := KroneckerProduct(D ^ QuoInt(q + 1, 4), 
                                                      IdentityMat(m, F));
                    # det(generator * scalingMatrix) = -1 * (-1) = 1
                    Add(generatorsOfHInSU,(generator * scalingMatrix));
                fi;
            fi;
        od;
    fi;

    U := KroneckerProduct(D, D ^ (-1));
    for i in [3..t] do
        U := KroneckerProduct(U, IdentityMat(m, F));
    od;
    # det(U) = 1
    E := D ^ QuoInt(Gcd(q + 1, d), Gcd(q + 1, m ^ (t - 1)));
    for i in [2..t] do
        E := KroneckerProduct(E, IdentityMat(m, F));
    od;
    # det(E) = zeta ^ ((1 - q) * Gcd(q + 1, d) / Gcd(q + 1, m ^ (t - 1)) * m ^ (t - 1))
    #        = zeta ^ ((1 - q) * Gcd(q + 1, d) / Gcd(q + 1, d / m) * d / m))

    # Write mu = zeta ^ ((q - 1) * k) for some k. We want 
    # det(mu * I_d) = zeta ^ ((q - 1) * Gcd(q + 1, d)), hence
    # (q - 1) * k * d = (q - 1) * Gcd(q + 1, d) mod (q ^ 2 - 1).
    # Divide through by (q - 1) and Gcd(q + 1, d) to obtain
    # k * d / Gcd(q + 1, d) = 1 mod ((q + 1) / Gcd(q + 1, d)). 
    # Now d / Gcd(q + 1, d) is invertible and we can take 
    # k = 1 / (d / Gcd(q + 1, d)) mod ((q + 1) / Gcd(q + 1, d)).
    k := 1 / (d / Gcd(q + 1, d)) mod ((q + 1) / Gcd(q + 1, d));
    mu := zeta ^ ((q - 1) * k);
    S := mu ^ (d / (Gcd(q + 1, d / m) * m)) * IdentityMat(d, F);
    # det(S) = det(mu * I_d) ^ (d / (Gcd(q + 1, d / m) * m))
    #        = zeta ^ ((q - 1) * Gcd(q + 1, d) / Gcd(q + 1, d / m) * d / m)
    #        = det(E) ^ (-1)

    # Size according to Table 2.10 of [BHR13]
    if t = 2 and m mod 4 = 2 and q mod 4 = 1 then
        size := Gcd(q + 1, m) * SizePSU(m, q) ^ 2 * Gcd(q + 1, m) ^ 2;
    else
        size := Gcd(q + 1, m) * SizePSU(m, q) ^ t 
                              * Gcd(q + 1, m ^ (t - 1)) * Gcd(q + 1, m) ^ (t - 1) 
                              * Factorial(t);
    fi;

    result := MatrixGroupWithSize(F, Concatenation(generatorsOfHInSU, [C, U, S * E]), size);
    SetInvariantSesquilinearForm(result, rec(matrix := AntidiagonalMat(d, F)));
    return ConjugateToStandardForm(result, "U", F);
end);

# Construction as in Proposition 10.2 in [HR05]
BindGlobal("TensorInducedDecompositionStabilizerInSp",
function(m, t, q)
    local field, I, gens, D, result, standardForm, formMatrix;

    if IsOddInt(m) then
        ErrorNoReturn("<m> must be even");
    fi;

    if IsEvenInt(t) then
        ErrorNoReturn("<t> must be odd");
    fi;

    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be odd");
    fi;

    field := GF(q);
    I := IdentityMat(m ^ (t - 2), field);

    gens := List(GeneratorsOfGroup(TensorWreathProduct(Sp(m, q), SymmetricGroup(t))));
    
    D := NormSpMinusSp(m, q);
    Add(gens, KroneckerProduct(KroneckerProduct(D, Inverse(D)), I));

    # Size according to the aforementioned proposition, but we add a
    # factor of 2 because we want the size of G, not of G / Z(G)
    result := MatrixGroupWithSize(field, gens, SizeSp(m, q) ^ t * Factorial(t));

    # Calculate the form preserved by the constructed group
    standardForm := AntidiagonalHalfOneMat(m, field);
    formMatrix := LiftFormsToTensorProduct(ListWithIdenticalEntries(t, standardForm), field);
    SetInvariantBilinearForm(result, rec(matrix := formMatrix));

    return ConjugateToStandardForm(result, "S", field);
end);

# Construction as in Lemma 10.3 in [HR10]
BindGlobal("SymplecticTensorInducedDecompositionStabilizerInOmega",
function(m, t, q)
    local field, one, evilCase, size, gens, I, D, result, d, l, Q, gen, F;

    if IsOddInt(m) then
        ErrorNoReturn("<m> must be even");
    fi;

    if IsOddInt(q * t) then
        ErrorNoReturn("<q> * <t> must be even");
    fi;

    if t < 2 then
        ErrorNoReturn("<t> must be at least 2");
    fi;
    
    if m = 2 and q in [2, 3] then
        ErrorNoReturn("(<m>, <q>) = (2, 2) and (<m>, <q>) = (2, 3) are disallowed");
    fi;

    field := GF(q);
    one := One(field);

    # This case is evil
    evilCase := m mod 4 = 2 and t = 2;

    if evilCase then

        gens := [];
        I := IdentityMat(m, field);
        for gen in GeneratorsOfGroup(Sp(m, q)) do
            Add(gens, KroneckerProduct(gen, I));
            Add(gens, KroneckerProduct(I, gen));
        od;

        # In this case the group is isomorphic to the central product
        # Sp(m, q) \circ Sp(m, q) according to [KL90] as well as [BHR13],
        # contrary to the structure Sp(m, q) \times Sp(m, q) given by [HR10].
        # Since |Z(Sp(m, q))| = (2, q - 1) we divide out that factor.
        size := QuoInt(SizeSp(m, q) ^ 2, Gcd(2, q - 1));

    else

        gens := List(GeneratorsOfGroup(TensorWreathProduct(Sp(m, q), SymmetricGroup(t))));

        # Size according to Table 2.10 of [BHR13]
        size := SizeSp(m, q) ^ t * Factorial(t);

    fi;

    # We must now construct the preserved form. [HR10] only tells us how to
    # do this for odd q, but the case of even q is fairly simple:
    # The group already preserves our standard form, since the corresponding
    # bilinear form is the standard symplectic one (recall -1 = 1 here) and
    # the diagonal is all zeros.
    if IsEvenInt(q) then

        Q := StandardOrthogonalForm(1, m ^ t, q).Q;

    else

        if not evilCase then
            # In the evil case this matrix has determinant 1, so we only
            # add it here.
            I := IdentityMat(m ^ (t - 2), field);
            D := NormSpMinusSp(m, q);
            Add(gens, KroneckerProduct(KroneckerProduct(D, Inverse(D)), I));
        fi;


        F := AntidiagonalHalfOneMat(m, field);
        Q := BilinearToQuadraticForm(LiftFormsToTensorProduct(ListWithIdenticalEntries(t, F), field));

    fi;

    result := MatrixGroupWithSize(field, gens, size);
    SetInvariantQuadraticFormFromMatrix(result, Q);
    return ConjugateToStandardForm(result, "O+", field);
end);

# Construction as in Lemma 10.4 in [HR10]
BindGlobal("OrthogonalOddTensorInducedDecompositionStabilizerInOmega",
function(m, t, q)
    local field, orthogonalGens, symmetricGroup, gens, I, S, T, _, F, result;

    if IsEvenInt(m) then
        ErrorNoReturn("<m> must be odd");
    fi;

    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be odd");
    fi;

    if m < 3 then
        ErrorNoReturn("<m> must be at least 3");
    fi;

    if t < 2 then
        ErrorNoReturn("<t> must be at least 2");
    fi;

    if m = 3 and q = 3 then
        ErrorNoReturn("the case (<m>, <q>) = (3, 3) is disallowed");
    fi;

    field := GF(q);

    orthogonalGens := AlternativeGeneratorsOfOrthogonalGroup(m, q, true);

    # [HR10] implicitly assumes that we generate the symmetric group Sym(t) with
    # an even permutation and the transposition (1, 2), which differs from the GAP-
    # standard of always using (1, ..., t) and (1, 2). Therefore, we create our own
    # copy of Sym(t) using (1, ..., t) if t is odd and (2, ..., t) if t is even as
    # our first generator.
    # If we did not do this, we would manually have to correct the determinant and
    # the spinor norm of the matrix corresponding to the first generator as we do
    # for the (1, 2)-matrix.
    symmetricGroup := Group(CycleFromList([1 + ((t - 1) mod 2)..t]), (1, 2));
    gens := List(GeneratorsOfGroup(TensorWreathProduct(Group(orthogonalGens.generatorsOfOmega), symmetricGroup)));
    Assert(0, Length(gens) = 4);
    Assert(0, IsMonomialMatrix(gens[4]));

    # Next we need to construct some elements of SO(m, q) TWr Sym(t). We only
    # need S to (potentially) correct the spinor norm of the (1, 2)-matrix later on.
    I := IdentityMat(m, field);
    S := KroneckerProduct(orthogonalGens.S, I);
    T := KroneckerProduct(orthogonalGens.S, orthogonalGens.S ^ -1);
    for _ in [1..t - 2] do
        S := KroneckerProduct(S, I);
        T := KroneckerProduct(T, I);
    od;

    # This one is obviously already in Omega(m ^ t, q).
    Add(gens, T);

    # According to Equation 4.7.8 in [KL90], we have to correct the determinant
    # of the (1, 2)-matrix in this case.
    if m mod 4 = 3 then
        gens[4] := -gens[4];
    fi;

    # We might also need to correct the spinor norm.
    F := IdentityMat(m ^ t, field);
    if FancySpinorNorm(F, field, gens[4]) = -1 then
        gens[4] := S * gens[4];
    fi;

    # Size according to Table 2.10 of [BHR13]
    result := MatrixGroupWithSize(field, gens, 2 ^ (t - 1) * SizeOmega(0, m, q) ^ t * Factorial(t));
    SetInvariantQuadraticFormFromMatrix(result, F / 2);
    return ConjugateToStandardForm(result, "O", field);
end);

# Construction as in Lemma 10.5 in [HR10]
BindGlobal("OrthogonalEvenTensorInducedDecompositionStabilizerInOmega",
function(epsilon, m, t, q)
    local d, field, zeta, I, squareDiscriminant, F, orthogonalGens,
    symmetricGroupGensAsMatrices, gens, SOGen, one, xi, alpha, beta,
    A, E, size, P, G, _, result;

    if IsOddInt(m) then
        ErrorNoReturn("<m> must be even");
    fi;

    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be odd");
    fi;

    if m < 5 + epsilon then
        ErrorNoReturn("<m> must be at least 5 + <epsilon>");
    fi;

    if t < 2 then
        ErrorNoReturn("<t> must be at least 2");
    fi;

    d := m ^ t;
    field := GF(q);
    zeta := PrimitiveElement(field);
    I := IdentityMat(m, field);

    squareDiscriminant := epsilon = (-1) ^ QuoInt((q - 1) * m, 4);
    F := IdentityMat(m, field);
    if not squareDiscriminant then
        F[1, 1] := zeta;
    fi;
    F := LiftFormsToTensorProduct(ListWithIdenticalEntries(t, F), field);
    orthogonalGens := AlternativeGeneratorsOfOrthogonalGroup(m, q, squareDiscriminant);

    # We first construct the group SO ^ epsilon(m, q) TWr Alt(t)
    # P is the matrix corresponding to the cycle (1, 2)
    # We can't just simply use the Group generated by (1, 2) for
    # the tensor wreath product instead of Sym(t) because GAP would
    # not know that the (1, 2)-cycle is supposed to be in Sym(t)
    # (and not just in Sym(2)) because GAP only considers the group's
    # 'largest moved point' which would be 2 instead of t if we used
    # Group((1, 2)) instead of SymmetricGroup(t).
    symmetricGroupGensAsMatrices := GeneratorsOfGroup(TensorWreathProduct(Group(I), SymmetricGroup(t)));
    if t = 2 then
        gens := [];
        for SOGen in Concatenation(orthogonalGens.generatorsOfOmega, [orthogonalGens.S]) do
            Add(gens, KroneckerProduct(SOGen, I));
            Add(gens, KroneckerProduct(I, SOGen));
        od;
        Assert(0, Length(symmetricGroupGensAsMatrices) = 2);
        P := symmetricGroupGensAsMatrices[2];
    else
        gens := List(GeneratorsOfGroup(TensorWreathProduct(Group(Concatenation(orthogonalGens.generatorsOfOmega, [orthogonalGens.S])), AlternatingGroup(t))));
        Assert(0, Length(symmetricGroupGensAsMatrices) = 3);
        P := symmetricGroupGensAsMatrices[3];
    fi;

    # The following is dark magic from Proposition 7.1 in [HR10], with
    # the idea being that alpha ^ 2 + beta ^ 2 = zeta.
    one := One(field);
    xi := PrimitiveElement(GF(q ^ 2));
    alpha := xi ^ QuoInt(q + 1, 2) * (xi - xi ^ q) / (xi + xi ^ q);
    beta := 2 * zeta / (xi + xi ^ q);
    A := [[alpha, beta], [beta, -alpha]];
    E := KroneckerProduct(IdentityMat(m / 2, field), A);
    if not squareDiscriminant then
        E{[1, 2]}{[1, 2]} := AntidiagonalMat([zeta, one], field);
    fi;

    # Size according to Table 2.10 of [BHR13], we have to add some
    # additional factors in the casework below
    size := 2 * SizeOmega(epsilon, m, q) ^ t;

    # now for some tedious casework, where we expand
    # SO ^ epsilon(m, q) TWr Alt(t) to GO ^ epsilon(m, q) TWr Sym(t)
    if t = 2 and m mod 4 = 2 then

        if squareDiscriminant then
            Add(gens, KroneckerProduct(orthogonalGens.G, I));
            Add(gens, KroneckerProduct(I, orthogonalGens.G));
        else
            Add(gens, KroneckerProduct(orthogonalGens.G, orthogonalGens.G ^ -1));
            Add(gens, KroneckerProduct(orthogonalGens.G * E, E ^ -1));
        fi;

        size := size * 4;

    elif t = 2 and m mod 4 = 0 and epsilon = -1 then

        Add(gens, KroneckerProduct(orthogonalGens.G, orthogonalGens.G ^ -1));
        Add(gens, KroneckerProduct(E, E ^ -1));

        if FancySpinorNorm(F, field, P) = 1 then
            Add(gens, P);
        else
            Add(gens, P * KroneckerProduct(orthogonalGens.G, I));
        fi;

        size := size * 8;

    elif t = 3 and m mod 4 = 2 and not squareDiscriminant then

        Add(gens, KroneckerProduct(KroneckerProduct(orthogonalGens.G, I), I));
        Add(gens, KroneckerProduct(KroneckerProduct(E, E ^ -1), I));

        size := size * 96;

    else

        G := KroneckerProduct(orthogonalGens.G, I);
        E := KroneckerProduct(E, E ^ -1);
        for _ in [1..t - 2] do
            G := KroneckerProduct(G, I);
            E := KroneckerProduct(E, I);
        od;
        Add(gens, G);
        Add(gens, E);
        Add(gens, P);

        size := size * 2 ^ (2 * t - 1) * Factorial(t);

    fi;

    result := MatrixGroupWithSize(field, gens, size);
    SetInvariantQuadraticFormFromMatrix(result, F / 2);
    return ConjugateToStandardForm(result, "O+", field);
end);
