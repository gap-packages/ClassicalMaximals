# Construction as in Lemma 9.1 of [2]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
OddExtraspecialGroup := function(r, m, q)
    local F, zeta, omega, X, Y, permutationMatrixEntries, listOfXi, listOfYi;

    if (q - 1) mod r <> 0 or not IsPrime(r) then
        ErrorNoReturn("<r> must be prime and a divisor of <q> - 1 but <r> = ", r,
                      " and <q> = ", q);
    fi;
    F := GF(q);
    zeta := PrimitiveElement(F);
    omega := zeta ^ (QuoInt(q - 1, r));
    X := DiagonalMat(List([0..r - 1], i -> omega ^ i));
    permutationMatrixEntries := Concatenation(List([1..r - 1], i -> [i, i + 1,
    zeta ^ 0]), [[r, 1, zeta ^ 0]]);
    Y := MatrixByEntries(F, r, r, permutationMatrixEntries);

    # It is a straightforward calculation to show that these matrices preserve
    # the unitary form given by the matrix I_d if one uses the fact that r | q + 1
    # in the unitary case.
    listOfXi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), F), X),
    IdentityMat(r ^ (i - 1), F)));
    listOfYi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), F), Y),
    IdentityMat(r ^ (i - 1), F)));

    return rec(listOfXi := listOfXi, listOfYi := listOfYi);
end;

# Construction as in Lemma 9.2 of [2]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
OddExtraspecialNormalizerInGL := function(r, m, q, type...)
    local F, zeta, omega, U, matrixIndices, entriesOfV, V, listOfUi,
        listOfVi, listForPermutation, w, W, listOfWi, generatingScalar, rootOfq,
        result;

    if Length(type) = 0 then
        type := "L";
    else
        type := type[1];
    fi;

    F := GF(q);
    zeta := PrimitiveElement(F);
    omega := zeta ^ (QuoInt(q - 1, r));
    U := DiagonalMat(List([1..r], i -> omega ^ (i * (i - 1) / 2)));
    matrixIndices := Concatenation(List([1..r], i -> List([1..r], j -> [i,
    j])));
    entriesOfV := List(matrixIndices, index -> Concatenation(index, [omega ^
    ((index[1] - 1) * (index[2] - 1))]));
    V := MatrixByEntries(F, r, r, entriesOfV);

    # Similarly to above, it is a straightforward calculation to show that the
    # matrices Ui preserve the unitary form given by the identity matrix
    listOfUi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), F), U),
    IdentityMat(r ^ (i - 1), F)));
    # The matrices Vi do not directly preserve the unitary form given by the
    # identity matrix, but rather preserve it *modulo a scalar*; namely, it is
    # straightforward to see Vi * I_d * HermitianConjugate(Vi) = r * I_d. This
    # "problem" will be taken care of eventually when we normalize determinants
    # in the function ExtraspecialNormalizerInSL.
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
    fi;
    result := OddExtraspecialGroup(r, m, q);
    result.generatingScalar := generatingScalar;
    result.listOfUi := listOfUi;
    result.listOfVi := listOfVi;
    result.listOfWi := listOfWi;
    return result;
end;

# Construction as in Lemma 9.3 of [2]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
SymplecticTypeNormalizerInGL := function(m, q, type...)
    local listOfUi, U, result, zeta, psi; 

    if (q - 1) mod 4 <> 0 or m < 2 then
        ErrorNoReturn("<q> must be 1 mod 4 and <m> must be at least 2 but <q> = ",
                      q, " and <m> = ", m);
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

    zeta := PrimitiveElement(GF(q));
    psi := zeta ^ (QuoInt(q - 1, 4));
    U := DiagonalMat([zeta ^ 0, psi]);
    # Determinant psi ^ (2 ^ (m - 1)) = (zeta ^ ((q - 1) / 2)) ^ (2 ^ (m - 2))
    # = (-1) ^ (2 ^ (m - 2)) = 1 if m >= 3 and = -1 if m = 2 (recall m >= 2).
    #
    # Again, it is straightforward to see that the Ui preserve the unitary form
    # given by the identity matrix (using the fact that 4 | q + 1 in the
    # unitary case with r = 2).
    listOfUi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(2 ^ (m - i), GF(q)), U),
    IdentityMat(2 ^ (i - 1), GF(q))));
    
    result.listOfUi := listOfUi;

    return result;
end;

# Construction as in Lemma 9.4 of [2]
Extraspecial2MinusTypeNormalizerInGL := function(m, q)
    local solutionQuadraticCongruence, a, b, kroneckerFactorX1, kroneckerFactorY1, 
    kroneckerFactorU1, kroneckerFactorV1, kroneckerFactorW1, result, p;

    if (q - 1) mod 2 <> 0 then
        ErrorNoReturn("<q> must be odd but <q> = ", q);
    fi;

    result := OddExtraspecialNormalizerInGL(2, m, q);
   
    p := PrimeDivisors(q)[1];
    solutionQuadraticCongruence := SolveQuadraticCongruence(-1, p);
    a := solutionQuadraticCongruence.a; 
    b := solutionQuadraticCongruence.b;

    # This has determinant 1 by construction of a and b
    kroneckerFactorX1 := Z(q) ^ 0 * [[a, b], [b, -a]];
    # Determinant 1
    kroneckerFactorY1 := Z(q) ^ 0 * [[0, -1], [1, 0]];
    # Determinant 2
    kroneckerFactorU1 := Z(q) ^ 0 * [[1, 1], [-1, 1]];
    # Determinant 4
    kroneckerFactorV1 := Z(q) ^ 0 * [[1 + a + b, 1 - a + b], 
                                     [-1 - a + b, 1 - a - b]];
    if m <> 1 then
        # Determinant 4
        kroneckerFactorW1 := Z(q) ^ 0 * [[1, 0, 1, 0], [0, 1, 0, 1], 
                                         [0, 1, 0, -1], [-1, 0, 1, 0]];
    fi;

    # TODO
    # It seems we don't need the Ui here, but just U1? 
    # --> Check this with the Magma code!
    result.listOfUi := [];
    # Determinant 1
    result.listOfXi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), GF(q)),
                                           kroneckerFactorX1);
    # Determinant 1
    result.listOfYi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), GF(q)),
                                           kroneckerFactorY1);
    # Determinant 2 ^ (2 ^ (m - 1))
    result.listOfUi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), GF(q)),
                                           kroneckerFactorU1);
    # Determinant 4 ^ (2 ^ (m - 1)) = 2 ^ (2 ^ m)
    result.listOfVi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), GF(q)),
                                           kroneckerFactorV1);
    if m <> 1 then
        # Determinant 4 ^ (2 ^ (m - 2)) = 2 ^ (2 ^ (m - 1))
        result.listOfWi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 2), GF(q)),
                                               kroneckerFactorW1);
    fi;

    return result;
end;

ScalarToNormalizeDeterminant := function(matrix, sizeOfMatrix, field)
    local scalar;
    scalar := RootFFE(field, Determinant(matrix), sizeOfMatrix);
    if scalar = fail then
        return fail;
    else
        return scalar ^ -1;
    fi;
end;

# Construction as in Proposition 9.5 of [2]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
OddExtraspecialNormalizerInSL := function(r, m, q, type...)
    local d, listOfUi, listOfVi, V, generatorsOfNormalizerInGL, scalarMultiplierUi, 
    scalarMultiplierVi, generators, generatingScalar, result, zeta, rootOfq;

    d := r ^ m;
    zeta := PrimitiveElement(GF(q));

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
                                * IdentityMat(d, GF(q));
    elif type = "U" then
        # remember that the variable q is actually q ^ 2 in the unitary case so
        # this is actually just q
        rootOfq := RootInt(q);
        generatingScalar := (zeta ^ (rootOfq - 1)) ^ QuoInt(rootOfq + 1,
                                                            Gcd(rootOfq + 1, d)) 
                                * IdentityMat(d, GF(q));
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

    scalarMultiplierVi := ScalarToNormalizeDeterminant(V, r, GF(q));
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
                                                               d, GF(q));
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
    result := Group(generators);
    # Size according to Table 2.9 of [1]
    if d = 3 and ((q - 4) mod 9 = 0 or (q - 7) mod 9 = 0) then
        SetSize(result, 27 * 8);
    elif type = "L" then
        SetSize(result, 
                Gcd(q - 1, d) * r ^ (2 * m) * Size(Sp(2 * m, r)));
    elif type = "U" then
        SetSize(result,
                Gcd(rootOfq + 1, d) * r ^ (2 * m) * Size(Sp(2 * m, r)));
    fi;
    return result;
end;

# Construction as in Proposition 9.5 of [2]
# If this function is called in the course of the computation of subgroups of
# SU(d, q) then the argument q of the function is actually q ^ 2.
SymplecticTypeNormalizerInSL := function(m, q, type...)
    local generatorsOfNormalizerInGL, d, listOfUi, listOfVi, listOfWi,
    generatingScalar, scalarMultiplierVi, i, scalarMultiplierUiAndWi, p, e, 
    factorization, generators, result, zeta, U1InGL, rootOfq;
    
    if (q - 1) mod 4 <> 0 or m < 2 then
        ErrorNoReturn("<q> must be 1 mod 4 and <m> must be at least 2 but <q> = ",
                      q, " and <m> = ", m);
    fi;

    if Length(type) = 0 then
        type := "L";
    else
        type := type[1];
    fi;

    d := 2 ^ m;
    # q = p ^ e with p prime
    factorization := PrimePowersInt(q);
    p := factorization[1];
    e := factorization[2];
    zeta := PrimitiveElement(GF(q));

    generatorsOfNormalizerInGL := SymplecticTypeNormalizerInGL(m, q, type);
    listOfUi := generatorsOfNormalizerInGL.listOfUi;
    listOfVi := generatorsOfNormalizerInGL.listOfVi;
    listOfWi := generatorsOfNormalizerInGL.listOfWi;

    # We always need a generating element of Z(SL(d, q))
    if type = "L" then
        generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, d))) 
                                * IdentityMat(d, GF(q));
    elif type = "U" then
        # remember that the variable q is actually q ^ 2 in the unitary case so
        # this is actually just q
        rootOfq := RootInt(q);
        generatingScalar := (zeta ^ (rootOfq - 1)) ^ QuoInt(rootOfq + 1,
                                                            Gcd(rootOfq + 1, d)) 
                                * IdentityMat(d, GF(q));
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
                                                               d, GF(q));
        elif type = "U" then
            # We have to be a bit more sophisticated in case U for the
            # generators to preserve the unitary form given by the identity
            # matrix.
            if (p ^ QuoInt(e, 2) - 7) mod 8 = 0 then 
                # This will give the expression Vi * I_d * HermitianConjugate(Vi)
                # and additional factor of 2 ^ (-1), which is what we need; see
                # the elif-case below, which is analogous, for more details.
                scalarMultiplierVi := RootFFE(GF(q), 4 * zeta ^ 0, 4) ^ (-1);
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
                i := RootFFE(GF(q), -1 * zeta ^ 0, 2);
                scalarMultiplierVi := RootFFE(GF(q), 2 * i, 2) ^ (-1);
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
                                                                d, GF(q));
        scalarMultiplierVi := ScalarToNormalizeDeterminant(listOfVi[1],
                                                           d, GF(q));
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

    result := Group(generators);

    # Size according to Table 2.9 of [1]
    if (d = 4 and (q - 5) mod 8 = 0 and type = "L") or
       (d = 4 and (p ^ QuoInt(e, 2) - 3) mod 8 = 0 and type = "U") then
        SetSize(result, 2 ^ 6 * Factorial(6) / 2);
    elif type = "L" then
        SetSize(result, 
                Gcd(q - 1, d) * 2 ^ (2 * m) * Size(Sp(2 * m, 2)));
    elif type = "U" then
        SetSize(result,
                Gcd(rootOfq + 1, d) * 2 ^ (2 * m) * Size(Sp(2 * m, 2)));
    fi;
    return result;
end;

# Construction as in Proposition 9.5 of [2]
# Only for d = 2
Extraspecial2MinusTypeNormalizerInSL := function(q)
    local generatorsOfNormalizerInGL, generatingScalar, p, e, V1, U1,
    factorization, generators, result, scalarMultiplierV1, scalarMultiplierU1,
    zeta;

    # q = p ^ e with p prime
    factorization := PrimePowersInt(q);
    p := factorization[1];
    e := factorization[2];
    zeta := PrimitiveElement(GF(q));

    generatorsOfNormalizerInGL := Extraspecial2MinusTypeNormalizerInGL(1, q);
    # Note that we only have the matrices X1, Y1, U1, V1
    U1 := generatorsOfNormalizerInGL.listOfUi[1];
    V1 := generatorsOfNormalizerInGL.listOfVi[1];

    # We always need a generating element of Z(SL(d, q))
    generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, 2))) *
    IdentityMat(2, GF(q));

    # Note that det(X1) = det(Y1) = 1, so we do not need to rescale these to
    # determinant 1. Furthermore, det(V1) = 4 and this is always a square, so
    # we can always rescale V1 to determinant 1.
    scalarMultiplierV1 := ScalarToNormalizeDeterminant(V1, 2, GF(q));
    V1 := scalarMultiplierV1 * V1;

    if IsEvenInt(e) or (p - 1) mod 8 = 0 or (p - 7) mod 8 = 0 then
        # These are the cases where we can find a square root of det(U1) = 2 in
        # GF(q) to rescale U1 to determinant 1.
        scalarMultiplierU1 := ScalarToNormalizeDeterminant(U1, 2, GF(q));
        U1 := scalarMultiplierU1 * U1;

        generators := Concatenation([generatingScalar],
                                    generatorsOfNormalizerInGL.listOfXi,
                                    generatorsOfNormalizerInGL.listOfYi,
                                    [U1, V1]);

    else
        # According to the Magma code, there is no need to take another
        # generator instead of U1 if we cannot rescale it to determinant 1 - we
        # simply discard U1 as a generator.
        generators := Concatenation([generatingScalar],
                                    generatorsOfNormalizerInGL.listOfXi,
                                    generatorsOfNormalizerInGL.listOfYi,
                                    [V1]);
    fi;

    result := Group(generators);
    # Size according to Table 2.9 of [1]
    if (q - 1) mod 8 = 0 or (q - 7) mod 8 = 0 then
        SetSize(result, 2 * Factorial(4));
    else
        SetSize(result, Factorial(4));
    fi;
    return result;
end;

BindGlobal("ExtraspecialNormalizerInSL",
function(r, m, q)
    if IsOddInt(r) then
        return OddExtraspecialNormalizerInSL(r, m, q);
    elif m >= 2 then
        # r = 2 and m >= 2
        return SymplecticTypeNormalizerInSL(m, q);
    else
        # r = 2 and m = 1
        return Extraspecial2MinusTypeNormalizerInSL(q);
    fi;
end);

# Construction as in Proposition 9.5 of [2]
BindGlobal("ExtraspecialNormalizerInSU",
function(r, m, q)
    local result;
    if not r ^ m > 2 then
        ErrorNoReturn("<r> ^ <m> must be at least 2 in the unitary case, but",
                      " <r> = ", r, " and <m> = ", m);
    elif not (q + 1) mod r = 0 or (IsEvenInt(r) and not (q + 1) mod 4 = 0) then
        ErrorNoReturn("<q> + 1 must be divisible by r (or 4 if r = 2) in the ",
                      "unitary case, but <q> =", q, " and <r> =", r);
    fi;

    if IsOddInt(r) then 
        result := OddExtraspecialNormalizerInSL(r, m, q ^ 2, "U");
    else
        result := SymplecticTypeNormalizerInSL(m, q ^ 2, "U");
    fi;
    
    # This group now preserves the unitary form given by the identity matrix
    # (see the constructor functions above for more info).
    # We conjugate the group so that it preserves the standard GAP form
    # Antidiag(1, ..., 1). 
    SetInvariantSesquilinearForm(result, rec(matrix := IdentityMat(r ^ m, GF(q ^ 2))));
    result := ChangeFixedSesquilinearForm(result,
                                          "U",
                                          AntidiagonalMat(List([1..r ^ m], i -> 1), GF(q ^ 2)));

    return result;
end);
