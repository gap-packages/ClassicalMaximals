# Construction as in Lemma 9.1 of [HR05]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
BindGlobal("OddExtraspecialGroup",
function(r, m, q)
    local F, zeta, omega, X, Y, listOfXi, listOfYi;

    if (q - 1) mod r <> 0 or not IsPrime(r) then
        ErrorNoReturn("<r> must be prime and a divisor of <q> - 1");
    fi;
    F := GF(q);
    zeta := PrimitiveElement(F);
    omega := zeta ^ (QuoInt(q - 1, r));
    X := DiagonalMat(List([0..r - 1], i -> omega ^ i));
    Y := PermutationMat(CycleFromList([1..r]), r, F);

    # It is a straightforward calculation to show that these matrices preserve
    # the unitary form given by the matrix I_d if one uses the fact that r | q + 1
    # in the unitary case.
    #
    # In the symplectic case, we have r = 2 and therefore omega = -1 and it is
    # also straightforward to check that these matrices preserve the symplectic
    # form given by the block-diagonal matrix consisting of blocks [[0, 1], [-1, 0]]
    listOfXi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), F), X),
    IdentityMat(r ^ (i - 1), F)));
    listOfYi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), F), Y),
    IdentityMat(r ^ (i - 1), F)));

    return rec(listOfXi := listOfXi, listOfYi := listOfYi);
end);

# Construction as in Lemma 9.2 of [HR05]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
BindGlobal("OddExtraspecialNormalizerInGL",
function(r, m, q, type...)
    local F, zeta, omega, U, V, listOfUi, listOfVi, listForPermutation,
        w, W, listOfWi, generatingScalar, rootOfq, result, i, j;

    if Length(type) = 0 then
        type := "L";
    else
        type := type[1];
    fi;

    F := GF(q);
    zeta := PrimitiveElement(F);
    omega := zeta ^ (QuoInt(q - 1, r));
    U := DiagonalMat(List([1..r], i -> omega ^ (i * (i - 1) / 2)));
    V := NullMat(r, r, F);
    for i in [1..r] do
        for j in [1..r] do
            V[i,j] := omega ^ ((i - 1) * (j - 1));
        od;
    od;
    V := ImmutableMatrix(F, V);

    # Similarly to above, it is a straightforward calculation to show that the
    # matrices Ui preserve the unitary form given by the identity matrix
    #
    # Again, in the symplectic case, one can easily check that the Ui preserve
    # the symplectic form given by the block-diagonal matrix consisting of
    # blocks [[0, 1], [-1, 0]] (recall that r = 2 in this case!)
    listOfUi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), F), U),
    IdentityMat(r ^ (i - 1), F)));
    # The matrices Vi do not directly preserve the unitary form given by the
    # identity matrix, but rather preserve it *modulo a scalar*; namely, it is
    # straightforward to see Vi * I_d * HermitianConjugate(Vi) = r * I_d. This
    # "problem" will be taken care of eventually when we normalize determinants
    # in the function ExtraspecialNormalizerInSL.
    #
    # In the same way, the matrices Vi scale the symplectic form given by the
    # block-diagonal matrix consisting of blocks [[0, 1], [-1, 0]] by a factor
    # of r = 2. This will be corrected later once we fix determinants.
    listOfVi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), F), V),
    IdentityMat(r ^ (i - 1), F)));

    if m <> 1 then
        # If m = 1 then we cannot have the Wi as generators since W is in 
        # GL(r ^ 2, q) (i.e. too large)

        listForPermutation := List([1..r ^ 2], 
                                   a -> (a + ((a - 1) mod r) * r) mod r ^ 2);
        # GAP lists start at index 1 so we have to make this fix: the element
        # mapped to 0 under the above operation is r and must be "re-mapped" to
        # r ^ 2 instead.
        listForPermutation[r] := r ^ 2;
        w := PermList(listForPermutation);
        W := Z(q) ^ 0 * PermutationMat(w, r ^ 2);
        # These matrices preserve the unitary form given by the identity matrix
        # as W is a permutation matrix.
        #
        # Similarly, one can check that they also preserve the symplectic form
        # given by the block-diagonal matrix consisting of blocks [[0, 1], [-1, 0]] 
        # (remember r = 2 in this case!)
        listOfWi := List([1..m - 1], 
                         i -> KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - 1 - i), 
                                                                            F), 
                                               W), IdentityMat(r ^ (i - 1), F)));
    else
        listOfWi := [];
    fi;

    if type = "L" then
        generatingScalar := zeta * IdentityMat(r ^ m, F);
    elif type = "U" then
        # remember that the variable q is actually q ^ 2 in the unitary case,
        # so this is actually q
        rootOfq := RootInt(q);
        generatingScalar := (zeta ^ (rootOfq - 1)) * IdentityMat(r ^ m, F);
    elif type = "S" then
        generatingScalar := -IdentityMat(r ^ m, F);
    fi;

    result := OddExtraspecialGroup(r, m, q);
    result.generatingScalar := generatingScalar;
    result.listOfUi := listOfUi;
    result.listOfVi := listOfVi;
    result.listOfWi := listOfWi;
    return result;
end);

# Construction as in Lemma 9.3 of [HR05]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
BindGlobal("SymplecticTypeNormalizerInGL",
function(m, q, type...)
    local F, listOfUi, U, result, zeta, psi; 

    if (q - 1) mod 4 <> 0 or m < 2 then
        ErrorNoReturn("<q> must be 1 mod 4 and <m> must be at least 2");
    fi;

    if Length(type) = 0 then
        type := "L";
    else
        type := type[1];
    fi;

    result := OddExtraspecialNormalizerInGL(2, m, q, type);
    
    # In fact, we do not need the matrix Z mentioned in Lemma 9.3: It is only
    # needed as a generator of the symplectic type subgroup of GL(d, q), but
    # not as a generator of its normalizer in GL(d, q) because for the
    # normalizer, we already need a generating scalar, i.e. a scalar matrix of
    # order q - 1 (whereas Z has only order (q - 1) / 4), making Z redundant.

    F := GF(q);
    zeta := PrimitiveElement(F);
    psi := zeta ^ (QuoInt(q - 1, 4));
    U := DiagonalMat([zeta ^ 0, psi]);
    # Determinant psi ^ (2 ^ (m - 1)) = (zeta ^ ((q - 1) / 2)) ^ (2 ^ (m - 2))
    # = (-1) ^ (2 ^ (m - 2)) = 1 if m >= 3 and = -1 if m = 2 (recall m >= 2).
    #
    # Again, it is straightforward to see that the Ui preserve the unitary form
    # given by the identity matrix (using the fact that 4 | q + 1 in the
    # unitary case with r = 2).
    listOfUi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(2 ^ (m - i), F), U),
    IdentityMat(2 ^ (i - 1), F)));
    
    result.listOfUi := listOfUi;

    return result;
end);

# Construction as in Lemma 9.4 of [HR05]
BindGlobal("Extraspecial2MinusTypeNormalizerInGL",
function(m, q, type...)
    local F, solutionQuadraticCongruence, a, b, kroneckerFactorX1, kroneckerFactorY1, 
    kroneckerFactorU1, kroneckerFactorV1, kroneckerFactorW1, result, p;

    if (q - 1) mod 2 <> 0 then
        ErrorNoReturn("<q> must be odd");
    fi;

    if Length(type) = 0 then
        type := "L";
    else
        type := type[1];
    fi;

    result := OddExtraspecialNormalizerInGL(2, m, q, type);
   
    F := GF(q);
    p := PrimeDivisors(q)[1];
    solutionQuadraticCongruence := SolveQuadraticCongruence(-1, p);
    a := solutionQuadraticCongruence.a; 
    b := solutionQuadraticCongruence.b;

    # This has determinant 1 by construction of a and b
    # 
    # It preserves the symplectic form given by the block-diagonal matrix
    # consisting of blocks [[0, -1], [1, 0]]
    kroneckerFactorX1 := Z(q) ^ 0 * [[a, b], [b, -a]];
    # Determinant 1
    #
    # Preserves the aforementioned symplectic form
    kroneckerFactorY1 := Z(q) ^ 0 * [[0, -1], [1, 0]];
    # Determinant 2
    #
    # Scales the aforementioned symplectic form by 2; this will be corrected
    # once we fix determinants later on
    kroneckerFactorU1 := Z(q) ^ 0 * [[1, 1], [-1, 1]];
    # Determinant 4
    #
    # Scales the aforementioned symplectic form by 4; this will be corrected
    # once we fix determinants later on
    kroneckerFactorV1 := Z(q) ^ 0 * [[1 + a + b, 1 - a + b], 
                                     [-1 - a + b, 1 - a - b]];
    if m <> 1 then
        # Determinant 4
        #
        # Scales the aforementioned symplectic form by 2; this will be
        # corrected once we fix determinants later on
        kroneckerFactorW1 := Z(q) ^ 0 * [[1, 0, 1, 0], [0, 1, 0, 1], 
                                         [0, 1, 0, -1], [-1, 0, 1, 0]];
    fi;

    result.listOfUi := [];
    # Determinant 1
    result.listOfXi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), F),
                                           kroneckerFactorX1);
    # Determinant 1
    result.listOfYi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), F),
                                           kroneckerFactorY1);
    # Determinant 2 ^ (2 ^ (m - 1))
    result.listOfUi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), F),
                                           kroneckerFactorU1);
    # Determinant 4 ^ (2 ^ (m - 1)) = 2 ^ (2 ^ m)
    result.listOfVi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), F),
                                           kroneckerFactorV1);
    if m <> 1 then
        # Determinant 4 ^ (2 ^ (m - 2)) = 2 ^ (2 ^ (m - 1))
        result.listOfWi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 2), F),
                                               kroneckerFactorW1);
    fi;

    return result;
end);

BindGlobal("ScalarToNormalizeDeterminant",
function(matrix, sizeOfMatrix, field)
    local scalar;
    scalar := RootFFE(field, Determinant(matrix), sizeOfMatrix);
    if scalar = fail then
        return fail;
    else
        return scalar ^ -1;
    fi;
end);

# Construction as in Proposition 9.5 of [HR05]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
BindGlobal("OddExtraspecialNormalizerInSL",
function(r, m, q, type...)
    local F, d, listOfUi, listOfVi, V, generatorsOfNormalizerInGL, scalarMultiplierUi, 
    scalarMultiplierVi, generators, generatingScalar, size, zeta, rootOfq;

    F := GF(q);
    d := r ^ m;
    zeta := PrimitiveElement(F);

    if Length(type) = 0 then
        type := "L";
    else
        type := type[1];
    fi;

    generatorsOfNormalizerInGL := OddExtraspecialNormalizerInGL(r, m, q, "U");
    listOfUi := generatorsOfNormalizerInGL.listOfUi;
    listOfVi := generatorsOfNormalizerInGL.listOfVi;
    # by construction of the Vi, this is V
    V := listOfVi[1]{[1..r]}{[1..r]};

    # We always need a generating element of Z(SL(d, q))
    if type = "L" then
        generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, d))) 
                                * IdentityMat(d, F);
    elif type = "U" then
        # remember that the variable q is actually q ^ 2 in the unitary case so
        # this is actually just q
        rootOfq := RootInt(q);
        generatingScalar := (zeta ^ (rootOfq - 1)) ^ QuoInt(rootOfq + 1,
                                                            Gcd(rootOfq + 1, d)) 
                                * IdentityMat(d, F);
    fi;

    # Note that not only det(Xi) = det(Yi) = 1, but as d is odd we
    # also have det(Wi) = 1, so these do not have to be rescaled to
    # determinant 1. However, we do not necessarily have det(Vi) = 1, but
    # in the case d odd, we can always rescale Vi to determinant 1 by
    # finding a d-th root of det(Vi) in GF(q) (which we can in turn do by
    # finding an r-th root of det(V) in GF(q) - this always exists: a somewhat
    # tricky calculation shows (det V) ^ 2 = (-1 / r) * r ^ r, where (-1 / r)
    # is the Legendre symbol). In particular, note that we have 
    # (det Vi) = (det V) ^ (r ^ (m - 1)).
    #
    # Scaling Vi like this will lead to Vi now actually preserving the unitary
    # form given by the identity matrix (and not only modulo scalars!). The
    # reason is as follows: We have det(V) ^ 2 = (-1 / r) * r ^ r, where 
    # (-1 / r) is the Legendre symbol. If q is even, the claim is trivial so
    # assume q is odd, hence q + 1 is even and divisible by r; the scalar
    # scalarMultiplierVi has the property that its (2r)-th power is det(V) ^ (-2)
    # and hence the expression Vi * I_d * HermitianConjugate(Vi) is multiplied
    # by the inverse of
    #
    #   (det(V) ^ 2) ^ ((q + 1) / (2 * r)) = ((-1 / r) * r ^ r) ^ ((q + 1) / 2 * r))
    #                                      = (-1 / r) ^ ((q + 1) / (2 * r)) * r ^ ((q + 1) / 2)
    #                                      = r * (-1 / r) ^ ((q + 1) / (2 * r)) * r ^ ((q - 1) / 2)
    #                                      = r * (-1 / r) ^ ((q + 1) / (2 * r)) * (r / q)
    # 
    # where we extended the definition of the Legendre symbol to finite fields
    # not necessarily of prime order. It can now be proved by distinguishing
    # the cases q = 1 and q = 3 mod 4 and applying quadratic reciprocity that
    # the last two factors just give 1 and so the expression 
    # Vi * I_d * HermitianConjugate(Vi) receives an additional factor r ^ (-1)
    # after rescaling Vi - which is exactly what we needed for Vi to preserve
    # the unitary form given by the identity matrix (see above).

    scalarMultiplierVi := ScalarToNormalizeDeterminant(V, r, F);
    listOfVi := List(listOfVi, Vi -> scalarMultiplierVi * Vi);

    if d = 3 then
        # In the case d <> 3 and d odd, we have det(Ui) = 1 and therefore
        # we do not need to rescale Ui to determinant 1.    
        # If d = 3, we can find a d-th root in GF(q) for det(Ui) if and
        # only if r ^ 2 | q - 1. If not, we append U1 ^ -1 * V1 * U1 
        # instead of U1 (note that m = 1) to the generating set (where V1 
        # is already normalized to determinant 1).

        if (q - 1) mod (r ^ 2) = 0 then
            # We can find a d-th root of det(Ui) = omega in GF(q), i.e. a
            # ninth root of unity. 
            #
            # Note that scaling by this factor does not
            # affect Ui preserving the unitary form given by the identity
            # matrix: Remember that the variable q in this function is actually
            # q ^ 2 in the unitary case. Now since (q ^ 2 - 1) = (q - 1)(q + 1) 
            # and r = 3 does not divide q - 1 in the unitary case, we have that if 
            # 9 | q ^ 2 - 1 then 9 | q + 1, which means the additional ninth root 
            # of unity will not affect the final expression 
            # Ui * I_d * HermitianConjugate(Ui).

            scalarMultiplierUi := ScalarToNormalizeDeterminant(listOfUi[1],
                                                               d, F);
            listOfUi := List(listOfUi, Ui -> scalarMultiplierUi * Ui);
        else
            # Note that Length(listOfUi) = m = 1 here and use 
            # U1 ^ -1 * V1 * U1 instead of U1

            listOfUi := [listOfUi[1] ^ -1 * listOfVi[1] * listOfUi[1]];
        fi;
    fi;

    generators := Concatenation([generatingScalar],
                                generatorsOfNormalizerInGL.listOfXi,
                                generatorsOfNormalizerInGL.listOfYi,
                                listOfUi, listOfVi,
                                generatorsOfNormalizerInGL.listOfWi);
    # Size according to Table 2.9 of [BHR13]
    if d = 3 and ((q - 4) mod 9 = 0 or (q - 7) mod 9 = 0) then
        size := 27 * 8;
    elif type = "L" then
        size := Gcd(q - 1, d) * r ^ (2 * m) * SizeSp(2 * m, r);
    elif type = "U" then
        size := Gcd(rootOfq + 1, d) * r ^ (2 * m) * SizeSp(2 * m, r);
    fi;

    return MatrixGroupWithSize(F, generators, size);
end);

# Construction as in Proposition 9.5 of [HR05]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
BindGlobal("SymplecticTypeNormalizerInSL",
function(m, q, type...)
    local F, generatorsOfNormalizerInGL, d, listOfUi, listOfVi, listOfWi,
    generatingScalar, scalarMultiplierVi, i, scalarMultiplierUiAndWi, p, e, 
    factorization, generators, size, zeta, U1InGL, rootOfq;
    
    if (q - 1) mod 4 <> 0 or m < 2 then
        ErrorNoReturn("<q> must be 1 mod 4 and <m> must be at least 2");
    fi;

    if Length(type) = 0 then
        type := "L";
    else
        type := type[1];
    fi;

    F := GF(q);
    d := 2 ^ m;
    # q = p ^ e with p prime
    factorization := PrimePowersInt(q);
    p := factorization[1];
    e := factorization[2];
    zeta := PrimitiveElement(F);

    generatorsOfNormalizerInGL := SymplecticTypeNormalizerInGL(m, q, type);
    listOfUi := generatorsOfNormalizerInGL.listOfUi;
    listOfVi := generatorsOfNormalizerInGL.listOfVi;
    listOfWi := generatorsOfNormalizerInGL.listOfWi;

    # We always need a generating element of Z(SL(d, q))
    if type = "L" then
        generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, d))) 
                                * IdentityMat(d, F);
    elif type = "U" then
        # remember that the variable q is actually q ^ 2 in the unitary case so
        # this is actually just q
        rootOfq := RootInt(q);
        generatingScalar := (zeta ^ (rootOfq - 1)) ^ QuoInt(rootOfq + 1,
                                                            Gcd(rootOfq + 1, d)) 
                                * IdentityMat(d, F);
    fi;

    # Note that det(Xi) = det(Yi) = 1, so we do not need to rescale these to
    # determinant 1.

    if m >= 3 then
        # If m >= 3, we have det(Wi) = det(Ui) = 1 and we do not have to
        # rescale these matrices to determinant 1. Furthermore, we can always
        # find a d-th root of det(Vi) in the case m >= 3; note that, again
        # det(Vi) is independent of i.

        if type = "L" then
            scalarMultiplierVi := ScalarToNormalizeDeterminant(listOfVi[1], 
                                                               d, F);
        elif type = "U" then
            # We have to be a bit more sophisticated in case U for the
            # generators to preserve the unitary form given by the identity
            # matrix.
            if (p ^ QuoInt(e, 2) - 7) mod 8 = 0 then 
                # This will give the expression Vi * I_d * HermitianConjugate(Vi)
                # and additional factor of 2 ^ (-1), which is what we need; see
                # the elif-case below, which is analogous, for more details.
                scalarMultiplierVi := RootFFE(F, 4 * zeta ^ 0, 4) ^ (-1);
            else
                # Remember that the variable q is actually q ^ 2 in the unitary
                # case so p ^ QuoInt(e, 2) is actually q. Since 4 | q + 1 in
                # the unitary case, this is q = 3 mod 8. Below, we construct a
                # fourth root of unity i in GF(q ^ 2) and then a square root of
                # 2i in GF(q ^ 2) (which exists!) - this will lead to 
                # Vi * I_d * HermitianConjugate(Vi) having an additional factor
                # of the *inverse* of
                #   (2i) ^ ((q + 1) / 2) = 2 * 2 ^ ((q - 1) / 2) * i ^ ((q + 1) / 2)
                #                        = 2 * (2 / q) * (-1)
                #                        = 2
                # by quadratic reciprocity, which is what we want.
                i := RootFFE(F, -1 * zeta ^ 0, 2);
                scalarMultiplierVi := RootFFE(F, 2 * i, 2) ^ (-1);
            fi;
        fi;

        listOfVi := List(listOfVi, Vi -> scalarMultiplierVi * Vi);
    
    elif ((q - 1) mod 8 = 0 and type = "L") or 
         ((p ^ QuoInt(e, 2) - 7) mod 8 = 0 and type = "U") then
        # This is m = 2 and q = 1 mod 8. Here we have det(Ui) = det(Wi) = -1
        # and we can find d-th roots for det(Ui) and det(Wi).
        #
        # This is also the case where we can find a d-th root for det(Vi):
        # For det(Vi) to have a d-th root in GF(q), we need e even or 
        # p = 1, 3, 7 mod 8; however, if e is even, then q = 1 mod 8, if e
        # is odd, then q = p ^ e = p mod 8 since p ^ 2 = 1 mod 8 and
        # because we only allow q = 1 mod 4, this reduces the condition 
        # p = 1, 3, 7 mod 8 to q = p = 1 mod 8.
        #
        # In the unitary case, remember that the variable q in this function is
        # actually q ^ 2 and hence the expression p ^ QuoInt(e, 2) above is
        # actually q. Similarly to above, the scaling factor for Ui and Wi 
        # (an eighth root of unity) will not affect the expressions 
        # Ui * I_d * HermitianConjugate(Ui) and analogously for Wi since 
        # 8 | q + 1 in this case; i.e., Ui and Wi will still preserve the
        # unitary form given by the identity matrix after scaling.
        # Although we could find eighth roots of unity
        # if 4 | q + 1 and not 8 | q + 1, rescaling the generators by those
        # would affect them preserving the unitary form given by the identity
        # matrix so we cannot do that.
        # Concerning Vi, one can compute that for d = 4, scaling the matrix
        # will lead to Vi * I_d * HermitianConjugate(Vi) having an additional
        # factor of 
        #   2 ^ (-1) * 2 ^ ((q - 1) / 2) = 2 ^ (-1) * (2 / q)
        # which is 2 ^ (-1) in this case by quadratic reciprocity and therefore
        # exactly what we need. Similarly to Ui and Wi, the result would come
        # out wrong if only 4 | q + 1 and not 8 | q + 1.

        scalarMultiplierUiAndWi := ScalarToNormalizeDeterminant(listOfUi[1],
                                                                d, F);
        scalarMultiplierVi := ScalarToNormalizeDeterminant(listOfVi[1],
                                                           d, F);
        listOfUi := List(listOfUi, Ui -> scalarMultiplierUiAndWi * Ui);
        listOfWi := List(listOfWi, Wi -> scalarMultiplierUiAndWi * Wi);
        listOfVi := List(listOfVi, Vi -> scalarMultiplierVi * Vi);
    else
        # If type = "L" then still m = 2 but now q <> 1 mod 8. Now we cannot 
        # rescale Wi and Ui to determinant 1 since det(Wi) = det(Ui) = -1 and 
        # there are no 8th roots of unity in GF(q). We cannot rescale Vi to 
        # determinant 1 either.
        # If type = "U" then either rescaling is impossible or, if it is
        # possible, it would mess up the property of the generators preserving
        # the unitary form given by the identity matrix.

        # Taking these elements instead of the Ui, Wi, Vi should suffice
        # according to the Magma code; note that they all have determinant 1.
        U1InGL := listOfUi[1];
        listOfUi := [listOfUi[1] ^ (-1) * listOfUi[2]];
        listOfWi := [U1InGL ^ (-1) * listOfWi[1]];
        listOfVi := [listOfVi[1] ^ (-1) * listOfVi[2]];
    fi;
    generators := Concatenation([generatingScalar],
                                generatorsOfNormalizerInGL.listOfXi,
                                generatorsOfNormalizerInGL.listOfYi,
                                listOfUi, listOfVi, listOfWi);

    # Size according to Table 2.9 of [BHR13]
    if (d = 4 and (q - 5) mod 8 = 0 and type = "L") or
       (d = 4 and (p ^ QuoInt(e, 2) - 3) mod 8 = 0 and type = "U") then
        size := 2 ^ 6 * Factorial(6) / 2;
    elif type = "L" then
        size := Gcd(q - 1, d) * 2 ^ (2 * m) * SizeSp(2 * m, 2);
    elif type = "U" then
        size := Gcd(rootOfq + 1, d) * 2 ^ (2 * m) * SizeSp(2 * m, 2);
    fi;

    return MatrixGroupWithSize(F, generators, size);
end);

# Construction as in Proposition 9.5 of [HR05]
# Only built for m = 1 if type = "L"
BindGlobal("Extraspecial2MinusTypeNormalizerInSL",
function(m, q, type...)
    local F, generatorsOfNormalizerInGL, generatingScalar, p, e, V1, U1,
    factorization, generators, size, scalarMultiplier, zeta, listOfVi, listOfWi;
    
    if Length(type) = 0 then
        type := "L";
    else
        type := type[1];
    fi;

    if type = "L" and m > 1 then
        ErrorNoReturn("If <type> = 'L', we must have <m> = 1");
    fi;

    F := GF(q);
    # q = p ^ e with p prime
    factorization := PrimePowersInt(q);
    p := factorization[1];
    e := factorization[2];
    zeta := PrimitiveElement(F);

    generatorsOfNormalizerInGL := Extraspecial2MinusTypeNormalizerInGL(m, q, type);
    U1 := generatorsOfNormalizerInGL.listOfUi[1];
    listOfVi := generatorsOfNormalizerInGL.listOfVi;
    listOfWi := generatorsOfNormalizerInGL.listOfWi;

    # We always need a generating scalar
    if type = "L" then
        generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, 2))) *
                            IdentityMat(2 ^ m, F);
    elif type = "S" then
        generatingScalar := -IdentityMat(2 ^ m, F);
    fi;

    # Note that det(Xi) = det(Yi) = 1, so we do not need to rescale these to
    # determinant 1. Similarly, det(Wi) = 1 for i >= 2.
    #
    # Furthermore, det(V1) = 2 ^ (2 ^ m) so we just have to rescale this by a
    # factor of 1 / 2; this also leads to V1 preserving the symplectic form
    # given by the block-diagonal matrix consisting of blocks [[0, 1], [-1, 0]]
    listOfVi[1] := 1 / 2 * listOfVi[1];

    # If type = "L", we have m = 1 and the only generator not considered yet is
    # U1. Then det(U1) = 2 and we need to find a square root of 2 in GF(q).
    #
    # If type = "S", we still have to consider U1, the Vi for i >= 2 and W1.
    # All these scale the symplectic form given by the block-diagonal matrix
    # consisting of blocks [[0, 1], [-1, 0]] by a factor of 2 so we need to
    # find a square root of 2 in GF(q) to fix this; this will also take care of
    # the determinants.
    if IsEvenInt(e) or (p - 1) mod 8 = 0 or (p - 7) mod 8 = 0 then
        # These are the cases where we can find a square root of 2 (by quadratic
        # reciprocity).
        scalarMultiplier := 1 / RootFFE(F, 2 * zeta ^ 0, 2);
        U1 := scalarMultiplier * U1;
        listOfVi{[2..m]} := List(listOfVi{[2..m]}, Vi -> scalarMultiplier * Vi);
        if m >= 2 then
            listOfWi[1] := scalarMultiplier * listOfWi[1];
        fi;

        generators := Concatenation([generatingScalar],
                                    generatorsOfNormalizerInGL.listOfXi,
                                    generatorsOfNormalizerInGL.listOfYi,
                                    [U1],
                                    listOfVi,
                                    listOfWi);

    else
        # Comparing with the Magma code, we can simply take 
        # U1 ^ (-1) * V2, U1 ^ (-1) * V3, ..., U1 ^ (-1) * Vm, U1 ^ (-1) * W1
        # in this case. 
        #
        # Observe that these all indeed have determinant 1 and
        # that they all preserve the symplectic form given by the
        # block-diagonal matrix consisting of blocks [[0, 1], [-1, 0]].
        listOfVi{[2..m]} := List(listOfVi{[2..m]}, Vi -> U1 ^ (-1) * Vi);
        if m >= 2 then
            listOfWi[1] := U1 ^ (-1) * listOfWi[1];
        fi;

        generators := Concatenation([generatingScalar],
                                    generatorsOfNormalizerInGL.listOfXi,
                                    generatorsOfNormalizerInGL.listOfYi,
                                    listOfVi,
                                    listOfWi);
    fi;

    # Size according to Table 2.9 of [BHR13]
    if type = "L" then
        if (q - 1) mod 8 = 0 or (q - 7) mod 8 = 0 then
            size := 2 * Factorial(4);
        else
            size := Factorial(4);
        fi;
    elif type = "S" then
        if (q - 1) mod 8 = 0 or (q - 7) mod 8 = 0 then
            size := 2 ^ (1 + 2 * m) * SizeSO(-1, 2 * m, 2);
        else
            size := 2 ^ (2 * m) * SizeSO(-1, 2 * m, 2);
        fi;
    fi;

    return MatrixGroupWithSize(F, generators, size);
end);

# Construction as in Proposition 9.1 of [HR10]
BindGlobal("Extraspecial2PlusTypeNormalizerInOmega",
function(m, q)
    local F, factorization, p, e, generatorsOfNormalizerInGL, listOfVi, 
    generatingScalar, rho, V1, generators, size;

    if m < 3 then
        ErrorNoReturn("<m> must be at least 3");
    fi;

    F := GF(q);
    # q = p ^ e with p prime
    factorization := PrimePowersInt(q);
    p := factorization[1];
    e := factorization[2];

    generatorsOfNormalizerInGL := OddExtraspecialNormalizerInGL(2, m, q);
    # Note that the matrices which are called Vi here are called Ui in [HR10]
    listOfVi := generatorsOfNormalizerInGL.listOfVi;

    # We always need a generating scalar
    # Cf. Lemma 3.3(2) in [HR10]
    generatingScalar := -IdentityMat(2 ^ m, F);

    # Notice that we already have det(Xi) = det(Yi) = det(Wi) = 1 and the
    # generators Ui are redundant due to Xi = Ui in this case.
    
    # Cf. Table 2.9 in [BHR13]
    size := 2 ^ (1 + 2 * m) * SizeSO(1, 2 * m, 2);
    
    if IsEvenInt(e) or (p - 1) mod 8 = 0 or (p + 1) mod 8 = 0 then
        # In this case we can find a square root of 2 in F; note that 
        # det(V) = -2 and hence det(Vi) = 2 ^ (2 ^ (m - 1))
        rho := RootFFE(F, 2 * One(F), 2);
        listOfVi := List(listOfVi, Vi -> rho ^ (-1) * Vi);
    else
        # Here we take Vi * V1 ^ (-1) as generators instead of Vi (notice that
        # this gives exactly the same group as the generators Vi * V{i+1} ^ (-1)
        # described in [HR10] since 
        #   (Vi * V1 ^ (-1)) * (V{i+1} * V1 ^ (-1)) ^ (-1) = Vi * V{i+1} ^ (-1) 
        # and
        #   (V1 * V2 ^ (-1)) * (V2 * V3 ^ (-1)) * ... * (V{i-1} * Vi ^ (-1)) = V1 * Vi ^ (-1) = (Vi * V1 ^ (-1)) ^ (-1)
        V1 := listOfVi[1];
        listOfVi := List(listOfVi, Vi -> Vi * V1 ^ (-1));

        size := size / 2;
    fi;

    generators := Concatenation([generatingScalar], 
                                generatorsOfNormalizerInGL.listOfXi, 
                                generatorsOfNormalizerInGL.listOfYi,
                                generatorsOfNormalizerInGL.listOfWi,
                                listOfVi);

    return MatrixGroupWithSize(F, generators, size);
end);

BindGlobal("ExtraspecialNormalizerInSL",
function(r, m, q)
    if IsOddInt(r) then
        return OddExtraspecialNormalizerInSL(r, m, q);
    elif m >= 2 then
        # r = 2 and m >= 2
        return SymplecticTypeNormalizerInSL(m, q);
    else
        # r = 2 and m = 1
        return Extraspecial2MinusTypeNormalizerInSL(m, q);
    fi;
end);

# Construction as in Proposition 9.5 of [HR05]
BindGlobal("ExtraspecialNormalizerInSU",
function(r, m, q)
    local F, result;
    if not r ^ m > 2 then
        ErrorNoReturn("<r> ^ <m> must be at least 2 in the unitary case");
    elif not (q + 1) mod r = 0 or (IsEvenInt(r) and not (q + 1) mod 4 = 0) then
        ErrorNoReturn("<q> + 1 must be divisible by r (or 4 if r = 2) in the ",
                      "unitary case");
    fi;

    F := GF(q ^ 2);
    if IsOddInt(r) then 
        result := OddExtraspecialNormalizerInSL(r, m, q ^ 2, "U");
    else
        result := SymplecticTypeNormalizerInSL(m, q ^ 2, "U");
    fi;
    
    # This group now preserves the unitary form given by the identity matrix
    # (see the constructor functions above for more info).
    # We conjugate the group so that it preserves the standard GAP form
    # Antidiag(1, ..., 1). 
    SetInvariantSesquilinearForm(result, rec(matrix := IdentityMat(r ^ m, F)));
    result := ConjugateToStandardForm(result, "U", F);

    return result;
end);

# Construction as in Proposition 9.5 of [HR05]
BindGlobal("ExtraspecialNormalizerInSp",
function(m, q)
    local F, result, gramMatrix;
    if not 2 ^ m > 2 then
        ErrorNoReturn("2 ^ <m> must be at least 4 in the symplectic case");
    fi;
    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be odd");
    fi;

    F := GF(q);
    result := Extraspecial2MinusTypeNormalizerInSL(m, q, "S");

    # This group now preserves the symplectic form given by the block-diagonal
    # matrix consisting of blocks [[0, 1], [-1, 0]] (see the constructor
    # functions above for more info).
    # We conjugate the group so that it preserves the standard GAP form
    # Antidiag(1, ..., 1, -1, ..., -1).
    gramMatrix := MatrixByEntries(F, 2 ^ m, 2 ^ m, 
                                  Concatenation(List([1..2 ^ (m - 1)], 
                                                     i -> [2 * i - 1, 2 * i, 1]),
                                                List([1..2 ^ (m - 1)],
                                                     i -> [2 * i, 2 * i - 1, -1])));
    SetInvariantBilinearForm(result, rec(matrix := gramMatrix));
    result := ConjugateToStandardForm(result, "S", F);

    return result;
end);

# Construction as in Proposition 9.1 of [HR10]
BindGlobal("ExtraspecialNormalizerInOmega",
function(m, q)
    local F, result;
    if not 2 ^ m > 4 then
        ErrorNoReturn("2 ^ <m> must be at least 8 in the orthogonal case");
    fi;

    F := GF(q);
    result := Extraspecial2PlusTypeNormalizerInOmega(m, q);
    
    # This group now preserves the bilinear form given by the identity matrix
    # and we conjugate it so that it preserves the standard GAP form
    SetInvariantBilinearForm(result, rec(matrix := IdentityMat(2 ^ m, F)));
    result := ConjugateToStandardForm(result, "O+", F);

    return result;
end);
