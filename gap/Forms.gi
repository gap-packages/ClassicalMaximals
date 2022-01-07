# One needs to ensure that the attribute DefaultFieldOfMatrixGroup is set
# correctly for <group>; this can be done, for example, by making the
# generators used during construction of the group immutable matrices over the
# appropriate field.
InstallGlobalFunction("ConjugateToSesquilinearForm",
function(group, type, gramMatrix)
    local gapForm, newForm, gapToCanonical, canonicalToNew, field, formMatrix,
        result, d, q, broadType;
    if not type in ["S", "O-B", "O-Q", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O-B', 'O-Q'");
    fi;
    d := DimensionOfMatrixGroup(group);
    field := DefaultFieldOfMatrixGroup(group);
    if type = "S" or type = "O-B" then
        if type = "S" then
            broadType := type;
        else
            broadType := "O";
        fi;
        formMatrix := BilinearForm(group, broadType);
        if formMatrix = fail then
            if type = "S" then
                ErrorNoReturn("No preserved symplectic form found for <group>");
            else
                ErrorNoReturn("No preserved symmetric bilinear form found for", 
                              " <group>");
            fi;
        fi;
        gapForm := BilinearFormByMatrix(formMatrix, field);
        newForm := BilinearFormByMatrix(gramMatrix, field);
    elif type = "U" then
        if IsOddInt(DegreeOverPrimeField(field)) then
            q := Size(field);
            field := GF(q ^ 2);
        fi;
        formMatrix := UnitaryForm(group);
        if formMatrix = fail then
            ErrorNoReturn("No preserved unitary form found for <group>");
        fi;
        gapForm := HermitianFormByMatrix(formMatrix, field);
        newForm := HermitianFormByMatrix(gramMatrix, field);
    else
        # This is the case type = "O-Q"
        formMatrix := QuadraticForm(group);
        if formMatrix = fail then
            ErrorNoReturn("No preserved quadratic form found for <group>");
        fi;
        gapForm := QuadraticFormByMatrix(formMatrix, field);
        newForm := QuadraticFormByMatrix(gramMatrix, field);
    fi;
    if gapForm = newForm then
        # nothing to be done
        result := group;
    # The Forms package has a bug for d = 1 so we need to make this exception
    elif d <> 1 then
        # the following if condition can only ever be fulfilled if <group> is an
        # orthogonal group; there the case of even dimension is problematic since,
        # in that case, there are two similarity classes of bilinear forms
        if not WittIndex(gapForm) = WittIndex(newForm) then
            ErrorNoReturn("The form preserved by <group> must be similar to the form ", 
                          "described by the Gram matrix <gramMatrix>.");
        fi;
        gapToCanonical := BaseChangeHomomorphism(BaseChangeToCanonical(gapForm), 
                                                 field);
        canonicalToNew := BaseChangeHomomorphism(BaseChangeToCanonical(newForm) ^ (-1), 
                                                 field);
        result := MatrixGroup(field, canonicalToNew(gapToCanonical(GeneratorsOfGroup(group))));
    
        # Set useful attributes
        UseIsomorphismRelation(group, result);
    else
        # replaces the Witt index check above
        if IsZero(gramMatrix) <> IsZero(formMatrix) then
            ErrorNoReturn("The form preserved by <group> must be similar to the",
                          " form described by the Gram matrix <gramMatrix>.");
        fi;
        result := group;
    fi;

    if type = "S" or type = "O-B" then
        SetInvariantBilinearForm(result, rec(matrix := gramMatrix));
    elif type = "U" then
        SetInvariantSesquilinearForm(result, rec(matrix := gramMatrix));
    else
        SetInvariantQuadraticFormFromMatrix(result, gramMatrix);
    fi;

    return result;
end);

# If <group> preserves a sesquilinear form of type <type> (one of "S", "U", "O"
# (in odd dimension), "O+" or "O-" (both in even dimension), return a group
# conjugate to <group> preserving the standard form of that type.
#
# Also, one need to ensure that the attribute DefaultFieldOfMatrixGroup is set
# correctly for <group>; this can be done, for example, by making the
# generators used during construction of the group immutable matrices over the
# appropriate field.
InstallGlobalFunction("ConjugateToStandardForm",
function(group, type)
    local d, F, q, gapForm, broadType;

    # determining d (dimension of matrix group), F (base field) and q (order of
    # F) plus some sanity checks
    if not type in ["S", "O+", "O-", "O", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O+', 'O-', 'O'");
    fi;
    F := DefaultFieldOfMatrixGroup(group);
    d := DimensionOfMatrixGroup(group);
    if type = "O" and IsEvenInt(d) then
        ErrorNoReturn("<type> cannot be 'O' if the dimension of <group> is even");
    elif type in ["O+", "O-"] and IsOddInt(d) then
        ErrorNoReturn("<type> cannot be 'O+' or 'O-' if the dimension of",
                      " <group> is odd");
    elif IsEvenInt(Size(F)) and IsOddInt(d) and type in ["O+", "O-", "O"] then
        ErrorNoReturn("If <type> is 'O+', 'O-' or 'O' and the size of <F> is",
                      " even, <d> must be even");
    fi;
    if type in ["S", "O", "O+", "O-"] then
        q := Size(F);
    else
        if IsSquareInt(Size(F)) then
            q := RootInt(Size(F));
        else
            # It might be that G is to be understood as a matrix group over 
            # GF(q ^ 2), but the matrices can actually be represented over a
            # smaller field, which causes DefaultFieldOfMatrixGroup to return GF(q)
            # instead of GF(q ^ 2) - we have to remedy this somehow ...
            q := Size(F);
        fi;
    fi;
    
    # get standard GAP form
    if type = "S" then
        gapForm := InvariantBilinearForm(Sp(d, q)).matrix;
    elif type = "U" then
        gapForm := InvariantSesquilinearForm(GU(d, q)).matrix;
    elif type = "O" then
        gapForm := InvariantBilinearForm(Omega(d, q)).matrix;
    elif type = "O+" then
        if Characteristic(F) = 2 then
            gapForm := InvariantQuadraticForm(Omega(1, d, q)).matrix;
        else
            gapForm := InvariantBilinearForm(Omega(1, d, q)).matrix;
        fi;
    elif type = "O-" then
        if Characteristic(F) = 2 then
            gapForm := InvariantQuadraticForm(Omega(-1, d, q)).matrix;
        else
            gapForm := InvariantBilinearForm(Omega(-1, d, q)).matrix;
        fi;
    fi;

    if type in ["O", "O+", "O-"] then
        if Characteristic(F) = 2 then
            broadType := "O-Q";
        else
            broadType := "O-B";
        fi;
    else
        broadType := type;
    fi;

    return ConjugateToSesquilinearForm(group, broadType, gapForm);
end);

# Let <dims> = [d1, d2, ..., dt], consider the tensor product of the vector
# spaces F ^ d1, F ^ d2, ..., F ^ dt and in it the i-th basis vector ei. 
#
# Return a list of indices [i1, i2, ..., it] such that ei is the tensor product 
# of the basis vectors ei1, ei2, ..., eit of F ^ d1, F ^ d2, ..., F ^ dt.
BindGlobal("GetTensorFactors",
function(i, dims)
    local d, t, q, s, r, result;

    d := Product(dims);
    t := Length(dims);
    if i > d or i < 1 then
        ErrorNoReturn("<i> must be between 0 and the product of all elements",
                      " of <dims>");
    fi;

    result := [];
    q := i - 1;
    for s in [0..t - 1] do
        s := t - s;
        r := q mod dims[s];
        result := Concatenation([r + 1], result);
        q := QuoInt(q, dims[s]);
    od;

    return result;
end);

# Let <forms> = [f1, f2, ..., ft] be a list of sesquilinear forms on the vector
# spaces F ^ d1, F ^ d2, ..., F ^ dt. Then we can lift these to a sesquilinear
# form f on the tensor product F ^ d1 x F ^ d2 x ... x F ^ dt by defining
# f(v1 x v2 x ... x vt, w1 x w2 x ... x wt) = f1(v1, w1)f2(v2, w2)...ft(vt, wt).
#
# Return the Gram matrix of f; the forms f1, f2, ..., ft must be given as their
# respective Gram matrices.
BindGlobal("LiftFormsToTensorProduct",
function(forms, F)
    local dims, d, t, newForm, i, j, indicesi, indicesj;

    dims := List(forms, NrRows);
    d := Product(dims);
    t := Length(dims);
    newForm := NullMat(d, d, F);

    for i in [1..d] do
        indicesi := GetTensorFactors(i, dims);
        for j in [1..d] do
            indicesj := GetTensorFactors(j, dims);

            newForm[i, j] := Product([1..t], k -> (forms[k])[indicesi[k], indicesj[k]]);
        od;
    od;

    return newForm;
end);

# Return the standard orthogonal and corresponding bilinear form as used for
# constructions in [HR10], cf. section 3.1 loc. cit.
BindGlobal("StandardOrthogonalForm",
function(epsilon, d, q)
    local field, m, F, Q, gamma, xi;
    
    if not epsilon in [-1, 0, 1] then
        ErrorNoReturn("<epsilon> must be one of -1, 0, 1");
    fi;
    if epsilon = 0 and IsEvenInt(d) then
        ErrorNoReturn("<epsilon> must be one of -1 or 1 if <d> is even");
    fi;
    if epsilon <> 0 and IsOddInt(d) then
        ErrorNoReturn("<epsilon> must be 0 if <d> is odd");
    fi;
    if IsEvenInt(q) and IsOddInt(d) then
        ErrorNoReturn("<d> must be even if <q> is even");
    fi;

    field := GF(q);
    m := QuoInt(d, 2);
    F := AntidiagonalMat(d, field);

    if IsOddInt(d * q) then
        Q := AntidiagonalMat(One(field) * Concatenation(ListWithIdenticalEntries(m, 1),
                                                        [1 / 2],
                                                        ListWithIdenticalEntries(m, 0)),
                             field);
    else
        Q := AntidiagonalMat(One(field) * Concatenation(ListWithIdenticalEntries(m, 1),
                                                        ListWithIdenticalEntries(m, 0)),
                             field);
        if epsilon = -1 then
            if IsEvenInt(q) then
                gamma := FindGamma(q);
            else
                xi := PrimitiveElement(GF(q ^ 2));
                gamma := xi ^ (q + 1) * (xi + xi ^ q) ^ (-2);
            fi;

            F[m, m] := 2 * gamma ^ 0;
            F[m + 1, m + 1] := 2 * gamma;
            Q[m, m] := gamma ^ 0;
            Q[m + 1, m + 1] := gamma;
        fi;
    fi;

    return rec(Q := Q, F := F);
end);

BindGlobal("ConjugateModule",
function(M, q)
  return GModuleByMats(List(MTX.Generators(M), A -> ApplyFunctionToEntries(A, x -> x ^ q)), 
                       MTX.Field(M));
end);

# Assuming that the group G acts absolutely irreducibly, try to find a unitary
# form which is G-invariant or prove that no such form exists.
#
# We use this function instead of PreservedSesquilinearForms from the Forms
# package since PreservedSesquilinearForms seems to be buggy and unreliable. 
# As an example, take the group generated by
#     [   1    0    0  ]         [ z^39 z^9  z^24 ]
#     [ z^33 z^14 z^26 ]   and   [ z^25 z^16 z^6  ]
#     [ z^19 z^31 z^5  ]         [ z^7  z^32 z^28 ]
# where z = Z(49), which does preserve a unitary form, but this is not
# recognised by PreservedSesquilinearForms, even after some 1000 calls of the
# function.
#
# In general, this function should only be used if one can be sure that <G>
# preserves a unitary form (but one does not know which one). 
InstallGlobalFunction("UnitaryForm",
function(G)
    local d, F, q, M, inverseHermitianConjugateM, formMatrix, row, col, x,
    scalar, counter;

    d := DimensionOfMatrixGroup(G);
    F := DefaultFieldOfMatrixGroup(G);
    if not IsFinite(F) then
        ErrorNoReturn("The base field of <G> must be finite");
    fi;
    if not IsEvenInt(DegreeOverPrimeField(F)) then
        # It might be that G is to be understood as a matrix group over 
        # GF(q ^ 2), but the matrices can actually be represented over a
        # smaller field, which causes DefaultFieldOfMatrixGroup to return GF(q)
        # instead of GF(q ^ 2) - we have to remedy this somehow ...
        q := Size(F);
    else
        q := RootInt(Size(F));
    fi;

    # Return stored sesquilinear form if it exists and is hermitian
    if HasInvariantSesquilinearForm(G) then
        formMatrix := InvariantSesquilinearForm(G).matrix;
        if formMatrix = HermitianConjugate(formMatrix, q) then
            return ImmutableMatrix(F, formMatrix);
        fi;
    fi;

    M := GModuleByMats(GeneratorsOfGroup(G), F);
    # An element A of G acts as A ^ (-T) in MTX.DualModule(M) and hence as 
    # HermitianConjugate(A, q) ^ (-1) in inverseHermitianConjugateM
    inverseHermitianConjugateM := ConjugateModule(MTX.DualModule(M), q);

    counter := 0;
    scalar := fail;
    # As the MeatAxe is randomised, we might have to make some more trials to
    # find a preserved unitary form if there is one; breaking after 1000 trials
    # is just a "safety net" in case a group <G> that does not preserve a
    # unitary form is input.
    while scalar = fail and counter < 1000 do
        counter := counter + 1;

        # If f: M -> inverseHermitianConjugateM is an isomorphism, it must respect
        # multiplication by group elements, i.e. for A in G
        #       f(x * A) = f(x) * HermitianConjugate(A, q) ^ (-1).
        # Let f be given by the matrix F, i.e. f: x -> x * F. Then we have
        #       (x * A) * F = x * F * HermitianConjugate(A, q) ^ (-1).
        # Putting these results together for all vectors x gives
        #       A * F = F * HermitianConjugate(A, q) ^ (-1)
        # <==>  A * F * HermitianConjugate(A, q) = F,
        # which is what we need.
        formMatrix := MTX.IsomorphismModules(M, inverseHermitianConjugateM);

        # We now need to ensure that formMatrix is actually the matrix of a
        # unitary form, which can be achieved by multiplying it by a scalar
        if formMatrix <> fail then
            if formMatrix <> HermitianConjugate(formMatrix, q) then
                # find a non-zero entry of formMatrix
                row := First([1..d], x -> not IsZero(formMatrix[x]));
                col := First([1..d], x -> not IsZero(formMatrix[row][x]));
                if not IsZero(formMatrix[col, row]) then
                    # this must be 1 for formMatrix to be hermitian
                    x := formMatrix[row, col] * formMatrix[col, row] ^ (-q);
                    # multiplying formMatrix by scalar will ensure that x = 1, i.e. that
                    # formMatrix is hermitian
                    scalar := RootFFE(x, q - 1);
                fi;

                if IsZero(formMatrix[col, row]) or scalar = fail then
                    if not MTX.IsAbsolutelyIrreducible(M) then
                        ErrorNoReturn("UnitaryForm failed - group is not absolutely irreducible");
                    fi;
                    continue;
                fi;

                # make formMatrix hermitian
                formMatrix := scalar * formMatrix;
            fi;

            if formMatrix <> HermitianConjugate(formMatrix, q) and not MTX.IsAbsolutelyIrreducible(M) then
                ErrorNoReturn("UnitaryForm failed - group is not absolutely irreducible");
            fi;

            return ImmutableMatrix(F, formMatrix);
        fi;
    od;

    return fail;
end);

# Assuming that the group G acts absolutely irreducibly, try to find a
#   * symplectic form (if <type> = S) or a 
#   * symmetric bilinear form (if <type> = O)
# which is G-invariant or prove that no such form exists.
#
# We use this function instead of PreservedBilinearForms form the Forms package
# since PreservedBilinearForms seems to be buggy and unreliable (see also
# comment above UnitaryForm).
#
# In general, this function should only be used if one can be sure that <G>
# preserves a symplectic form (but one does not know which one).
InstallGlobalFunction("BilinearForm",
function(G, type)
    local F, M, inverseTransposeM, counter, formMatrix, condition;

    if not type in ["S", "O"] then
        ErrorNoReturn("<type> must be one of 'S', 'O'");
    fi;
    # Set the condition the Gram matrix needs to satisfy for each of the
    # possible types.
    if type = "S" then
        condition := x -> (x = - TransposedMat(x));
    elif type = "O" then
        condition := x -> (x = TransposedMat(x));
    fi;

    F := DefaultFieldOfMatrixGroup(G);

    # Return stored bilinear form if it exists and is symplectic / symmetric
    if HasInvariantBilinearForm(G) then
        formMatrix := InvariantBilinearForm(G).matrix;
        if condition(formMatrix) then
            return ImmutableMatrix(F, formMatrix);
        fi;
    fi;
    
    M := GModuleByMats(GeneratorsOfGroup(G), F);

    if not MTX.IsIrreducible(M) then
        ErrorNoReturn("BilinearForm failed - group is not irreducible");
    fi;

    # An element A of G acts as A ^ (-T) in MTX.DualModule(M) 
    inverseTransposeM := MTX.DualModule(M);

    counter := 0;
    # As the MeatAxe is randomised, we might have to make some more trials to
    # find a preserved symplectic / symmetric bilinear form if there is one; 
    # breaking after 1000 trials is just a "safety net" in case a group <G> 
    # that does not preserve a symplectic / symmetric bilinear form is input.
    while counter < 1000 do
        counter := counter + 1;

        # If f: M -> inverseTransposeM is an isomorphism, it must respect
        # multiplication by group elements, i.e. for A in G
        #       f(x * A) = f(x) * A ^ (-T)
        # Let f be given by the matrix F, i.e. f: x -> x * F. Then we have
        #       (x * A) * F = x * F * A ^ (-T)
        # Putting these results together for all vectors x gives
        #       A * F = F * A ^ (-T)
        # <==>  A * F * A ^ T = F,
        # which is what we need.
        formMatrix := MTX.IsomorphismModules(M, inverseTransposeM);

        if formMatrix <> fail then
            # check if formMatrix is antisymmetric
            if condition(formMatrix) then
                return ImmutableMatrix(F, formMatrix);
            fi;
            if not MTX.IsAbsolutelyIrreducible(M) then
                ErrorNoReturn("BilinearForm failed - group is not absolutely irreducible");
            fi;
        fi;
    od;

    return fail;
end);

InstallGlobalFunction("SymplecticForm",
function(G)
    return BilinearForm(G, "S");
end);

InstallGlobalFunction("SymmetricBilinearForm",
function(G)
    return BilinearForm(G, "O");
end);

InstallGlobalFunction("QuadraticForm",
function(G)
    local d, F, formMatrix, polarFormMatrix, i, g, RightSideForLinSys,
    MatrixForLinSys, x;

    d := DimensionOfMatrixGroup(G);
    F := DefaultFieldOfMatrixGroup(G);
    if not IsFinite(F) then
        ErrorNoReturn("The base field of <G> must be finite");
    fi;

    if HasInvariantQuadraticForm(G) then
        formMatrix := InvariantQuadraticForm(G).matrix;
        return ImmutableMatrix(F, formMatrix);
    fi;

    # We first look for an invariant symmetric bilinear form of G, which will
    # be the polar form of the desired quadratic form
    polarFormMatrix := SymmetricBilinearForm(G);
    # The Gram matrix formMatrix of the quadratic form is upper triangular and
    # polarFormMatrix = formMatrix + formMatrix ^ T, so the entries above the
    # main diagonal of polarFormMatrix and formMatrix must be the same
    formMatrix := List([1..d], i -> Concatenation(ListWithIdenticalEntries(i, Zero(F)),
                                                  polarFormMatrix[i]{[i + 1..d]}));
    if Characteristic(F) <> 2 then
        # In this case, the polar form determines the quadratic form completely
        formMatrix := formMatrix + 1 / 2 * DiagonalMat(DiagonalOfMatrix(polarFormMatrix));
    else
        # We are left to determine the diagonal entries of formMatrix. Let them
        # be x1, ..., xd and X = diag(x1, ..., xd); furthermore, let U be the
        # part of polarFormMatrix above the main diagonal (i.e. the current
        # value of formMatrix). Then for the quadratic form X + U to be
        # preserved, we need g * (X + U) * g ^ T to have the same diagonal
        # entries as X + U, i.e. as X, for each generator g of G.
        #
        # Hence, we need xi = (g * U * g ^ T)_ii + (x1 * g[i, 1] ^ 2 + ... + xd * g[i, d] ^ 2)
        # This leads to a linear system for the xi, which we solve.

        RightSideForLinSys := Concatenation(List(GeneratorsOfGroup(G), 
                                                 g -> DiagonalOfMatrix(g * formMatrix * TransposedMat(g))));
        MatrixForLinSys := Concatenation(List(GeneratorsOfGroup(G),
                                              g -> List([1..d], 
                                                        i -> DiagonalOfMatrix(TransposedMat([g[i]{[1..d]}]) * [g[i]{[1..d]}]))
                                                    + IdentityMat(d, F)));
        x := SolutionMat(TransposedMat(MatrixForLinSys), RightSideForLinSys);

        if x = fail then
            return fail;
        fi;

        formMatrix := formMatrix + DiagonalMat(x);
    fi;

    return formMatrix;
end);
