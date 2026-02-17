BindGlobal( "CM_SetInvariantQuadraticFormFromMatrix", function( g, mat, F )
    SetInvariantQuadraticForm( g, rec( matrix:= mat, baseDomain:= F ) );
    SetInvariantBilinearForm( g, rec( matrix:= mat+TransposedMat(mat),
                                      baseDomain:= F ) );
end );


# Compute the Gram matrix of the quadratic form corresponding to the bilinear
# form described by <gramMatrix> in odd characteristic.
BindGlobal("BilinearToQuadraticForm",
function(gramMatrix)
    local F, n, i, Q;

    F := DefaultFieldOfMatrix(gramMatrix);

    if Characteristic(F) = 2 then
        ErrorNoReturn("Characteristic must be odd");
    fi;

    n := NrRows(gramMatrix);
    Q := List(gramMatrix, ShallowCopy);
    for i in [1..n] do
        Q{[i + 1..n]}{[i]} := NullMat(n - i, 1, F);
        Q[i, i] := gramMatrix[i, i] / 2;
    od;

    return Q;
end);

# Note that if type = "U" then `field` must be GF(q^2) for a subgroup of GU(d,q)
InstallGlobalFunction("ConjugateToSesquilinearForm",
function(group, type, gramMatrix, field)
    local gapForm, newForm, baseChangeMatrix, formMatrix,
        result, d, q, broadType;
    if not type in ["S", "O-B", "O-Q", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O-B', 'O-Q'");
    fi;
    d := DimensionOfMatrixGroup(group);
    if type = "S" or type = "O-B" then
        if type = "S" then
            broadType := type;
        else
            broadType := "O";
        fi;
        formMatrix := CM_BilinearForm(group, broadType, field);
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
        formMatrix := CM_UnitaryForm(group, field);
        if formMatrix = fail then
            ErrorNoReturn("No preserved unitary form found for <group>");
        fi;
        gapForm := HermitianFormByMatrix(formMatrix, field);
        newForm := HermitianFormByMatrix(gramMatrix, field);
    else
        # This is the case type = "O-Q"
        formMatrix := CM_QuadraticForm(group, field);
        if formMatrix = fail then
            ErrorNoReturn("No preserved quadratic form found for <group>");
        fi;
        gapForm := QuadraticFormByMatrix(formMatrix, field);
        newForm := QuadraticFormByMatrix(gramMatrix, field);
    fi;
    if gapForm = newForm then
        # nothing to be done
        result := group;
        result!.baseChangeMatrix := IdentityMat(d, field);
    # The Forms package has a bug for d = 1 so we need to make this exception
    elif d <> 1 then
        # the following if condition can only ever be fulfilled if <group> is an
        # orthogonal group; there the case of even dimension is problematic since,
        # in that case, there are two similarity classes of bilinear forms
        if not WittIndex(gapForm) = WittIndex(newForm) then
            ErrorNoReturn("The form preserved by <group> must be similar to the form ", 
                          "described by the Gram matrix <gramMatrix>.");
        fi;
        baseChangeMatrix := BaseChangeToCanonical(gapForm)^-1 * BaseChangeToCanonical(newForm);
        result := MatrixGroup(field, List(GeneratorsOfGroup(group), g -> g ^ baseChangeMatrix));
        result!.baseChangeMatrix := baseChangeMatrix;

        # Set useful attributes
        UseIsomorphismRelation(group, result);
    else
        # replaces the Witt index check above
        if IsZero(gramMatrix) <> IsZero(formMatrix) then
            ErrorNoReturn("The form preserved by <group> must be similar to the",
                          " form described by the Gram matrix <gramMatrix>.");
        fi;
        result := group;
        result!.baseChangeMatrix := IdentityMat(d, field);
    fi;

    if type = "S" then
        SetInvariantBilinearForm(result, rec(matrix := gramMatrix, baseDomain := field));
    elif type = "O-B" then
        CM_SetInvariantQuadraticFormFromMatrix(result, BilinearToQuadraticForm(gramMatrix), field);
    elif type = "U" then
        SetInvariantSesquilinearForm(result, rec(matrix := gramMatrix, baseDomain := field));
    else
        CM_SetInvariantQuadraticFormFromMatrix(result, gramMatrix, field);
    fi;

    return result;
end);

# If <group> preserves a sesquilinear form of type <type> (one of "S", "U", "O"
# (in odd dimension), "O+" or "O-" (both in even dimension), return a group
# conjugate to <group> preserving the standard form of that type.
InstallGlobalFunction("ConjugateToStandardForm",
function(group, type, field)
    local d, q, gapForm, broadType;

    # determining d (dimension of matrix group), F (base field) and q (order of
    # F) plus some sanity checks
    if not type in ["S", "O+", "O-", "O", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O+', 'O-', 'O'");
    fi;
    d := DimensionOfMatrixGroup(group);
    if type = "O" and IsEvenInt(d) then
        ErrorNoReturn("<type> cannot be 'O' if the dimension of <group> is even");
    elif type in ["O+", "O-"] and IsOddInt(d) then
        ErrorNoReturn("<type> cannot be 'O+' or 'O-' if the dimension of",
                      " <group> is odd");
    elif IsEvenInt(Size(field)) and IsOddInt(d) and type in ["O+", "O-", "O"] then
        ErrorNoReturn("If <type> is 'O+', 'O-' or 'O' and the size of <F> is",
                      " even, <d> must be even");
    fi;
    if type in ["S", "O", "O+", "O-"] then
        q := Size(field);
    else
        q := Characteristic(field) ^ (DegreeOverPrimeField(field)/2);
    fi;
    
    # get standard GAP form
    if type = "S" then
        gapForm := InvariantBilinearForm(Sp(d, q)).matrix;
    elif type = "U" then
        gapForm := InvariantSesquilinearForm(GU(d, q)).matrix;
    elif type = "O" then
        gapForm := InvariantBilinearForm(Omega(d, q)).matrix;
    elif type = "O+" then
        if Characteristic(field) = 2 then
            gapForm := InvariantQuadraticForm(Omega(1, d, q)).matrix;
        else
            gapForm := InvariantBilinearForm(Omega(1, d, q)).matrix;
        fi;
    elif type = "O-" then
        if Characteristic(field) = 2 then
            gapForm := InvariantQuadraticForm(Omega(-1, d, q)).matrix;
        else
            gapForm := InvariantBilinearForm(Omega(-1, d, q)).matrix;
        fi;
    fi;

    if type in ["O", "O+", "O-"] then
        if Characteristic(field) = 2 then
            broadType := "O-Q";
        else
            broadType := "O-B";
        fi;
    else
        broadType := type;
    fi;

    return ConjugateToSesquilinearForm(group, broadType, gapForm, field);
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
    local dims, d, t, newForm, i, j, iteri, iterj, indicesi, indicesj;

    dims := List(forms, NrRows);
    d := Product(dims);
    t := Length(dims);
    newForm := NullMat(d, d, F);
    dims := List(dims,d->[1..d]);

    iteri := IteratorOfCartesianProduct(dims);
    for i in [1..d] do
        indicesi := NextIterator(iteri);
        iterj := IteratorOfCartesianProduct(dims);
        for j in [1..d] do
            indicesj := NextIterator(iterj);
            newForm[i, j] := Product([1..t], k -> (forms[k])[indicesi[k], indicesj[k]]);
        od;
    od;

    return newForm;
end);

# Return the standard orthogonal and corresponding bilinear form as used for
# constructions in [HR10], cf. section 3.1 loc. cit.
InstallGlobalFunction("StandardOrthogonalForm",
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
InstallGlobalFunction("CM_UnitaryForm",
function(G, F)
    local d, q, M, inverseHermitianConjugateM, formMatrix, row, col, x,
    scalar;

    d := DimensionOfMatrixGroup(G);
    if not IsFinite(F) then
        ErrorNoReturn("The base field of <G> must be finite");
    fi;
    q := Characteristic(F) ^ (DegreeOverPrimeField(F)/2);

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
                scalar := RootFFE(F, x, q - 1);
            fi;

            if IsZero(formMatrix[col, row]) or scalar = fail then
                if not MTX.IsAbsolutelyIrreducible(M) then
                    ErrorNoReturn("CM_UnitaryForm failed - group is not absolutely irreducible");
                fi;
                ErrorNoReturn("RootFFE failed in CM_UnitaryForm");
            fi;

            # make formMatrix hermitian
            formMatrix := scalar * formMatrix;
        fi;

        # for more consistent results, make the first nonzero entry 1
        x := First(formMatrix[1], y -> not IsZero(y));
        if x <> fail and x = x^q then
            formMatrix := formMatrix * x^-1;
        fi;

        if formMatrix <> HermitianConjugate(formMatrix, q) and not MTX.IsAbsolutelyIrreducible(M) then
            ErrorNoReturn("CM_UnitaryForm failed - group is not absolutely irreducible");
        fi;

        return ImmutableMatrix(F, formMatrix);
    fi;

    return fail;
end);

# Assuming that the group G acts absolutely irreducibly, try to find a
#   * symplectic form (if <type> = S) or a 
#   * symmetric bilinear form (if <type> = O)
# which is G-invariant or prove that no such form exists.
#
# We use this function instead of PreservedBilinearForms form the Forms package
# since PreservedBilinearForms seems to be buggy and unreliable (see also
# comment above CM_UnitaryForm).
InstallGlobalFunction("CM_BilinearForm",
function(G, type, F)
    local M, inverseTransposeM, counter, formMatrix, condition, x;

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

    # Return stored bilinear form if it exists and is symplectic / symmetric
    if HasInvariantBilinearForm(G) then
        formMatrix := InvariantBilinearForm(G).matrix;
        if condition(formMatrix) then
            return ImmutableMatrix(F, formMatrix);
        fi;
    fi;
    
    M := GModuleByMats(GeneratorsOfGroup(G), F);

    if not MTX.IsIrreducible(M) then
        ErrorNoReturn("CM_BilinearForm failed - group is not irreducible");
    fi;

    # An element A of G acts as A ^ (-T) in MTX.DualModule(M) 
    inverseTransposeM := MTX.DualModule(M);

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
            # for more consistent results, make the first nonzero entry 1
            x := First(formMatrix[1], y -> not IsZero(y));
            formMatrix := formMatrix * x^-1;
            return ImmutableMatrix(F, formMatrix);
        fi;
        if not MTX.IsAbsolutelyIrreducible(M) then
            ErrorNoReturn("CM_BilinearForm failed - group is not absolutely irreducible");
        fi;
    fi;

    return fail;
end);

InstallGlobalFunction("CM_SymplecticForm",
function(G, F)
    return CM_BilinearForm(G, "S", F);
end);

InstallGlobalFunction("CM_SymmetricBilinearForm",
function(G, F)
    return CM_BilinearForm(G, "O", F);
end);

InstallGlobalFunction("CM_QuadraticForm",
function(G, F)
    local d, formMatrix, polarFormMatrix, i, g, RightSideForLinSys,
    MatrixForLinSys, x;

    d := DimensionOfMatrixGroup(G);
    if not IsFinite(F) then
        ErrorNoReturn("The base field of <G> must be finite");
    fi;

    if HasInvariantQuadraticForm(G) then
        formMatrix := InvariantQuadraticForm(G).matrix;
        return ImmutableMatrix(F, formMatrix);
    fi;

    # We first look for an invariant symmetric bilinear form of G, which will
    # be the polar form of the desired quadratic form
    polarFormMatrix := CM_SymmetricBilinearForm(G, F);
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

InstallGlobalFunction("CM_ClassicalForms",
function(G, field)
    local M, forms, form, formq, sign, type;
    
    M := GModuleByMats(GeneratorsOfGroup(G), field);
    if not MTX.IsAbsolutelyIrreducible(M) then
        ErrorNoReturn("CM_ClassicalForms: <G> must be irreducible");
    fi;
    forms := rec();
    forms.formType := "linear";
    forms.bilinearForm := false;
    forms.quadraticForm := false;
    forms.sesquilinearForm := false;

    form := CM_SymmetricBilinearForm(G, field);
    if form <> fail then
        forms.bilinearForm := form;
        formq := CM_QuadraticForm(G, field);
        if formq = fail then
            # should only happen in characteristic 2
            forms.formType := "symplectic";
            return forms;
        else
            sign := MTX.OrthogonalSign(M);
            Assert(0, sign in [-1, 0, 1]);
            if sign = 1 then
                type := "orthogonalplus";
            elif sign = -1 then
                type := "orthogonalminus";
            else
                type := "orthogonalcircle";
            fi;
            forms.formType := type;
            forms.quadraticForm := formq;
            forms.sign := sign;
            return forms;
        fi;
    fi;
    form := CM_SymplecticForm(G, field);
    if form <> fail then
        forms.formType := "symplectic";
        forms.bilinearForm := form;
        return forms;
    fi;
    if IsEvenInt(DegreeOverPrimeField(field)) then
        form := CM_UnitaryForm(G, field);
        if form <> fail then
            forms.formType := "unitary";
            forms.sesquilinearForm := form;
            return forms;
        fi;
    fi;
    return forms;
end);
