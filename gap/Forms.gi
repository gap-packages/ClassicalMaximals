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

# The kinds of forms below are "S" (symplectic), "U" (Hermitian, over
# <field> = GF(q ^ 2)), "O-B" (symmetric bilinear) and "O-Q" (quadratic).

# Return the matrix of the form of kind <kind> that the group G preserves:
# the stored form if there is one, else one found by the MeatAxe.
BindGlobal("CM_InvariantFormMatrix",
function(G, kind, field)
    local M;

    if kind in ["S", "O-B"] then
        M := CM_BilinearForm(G, field);
        if kind = "S" and (M = fail or M <> -TransposedMat(M)) then
            ErrorNoReturn("No preserved symplectic form found for <group>");
        elif kind = "O-B" and (M = fail or M <> TransposedMat(M)) then
            ErrorNoReturn("No preserved symmetric bilinear form found for <group>");
        fi;
    elif kind = "U" then
        M := CM_UnitaryForm(G, field);
        if M = fail then
            ErrorNoReturn("No preserved unitary form found for <group>");
        fi;
    else
        M := CM_QuadraticForm(G, field);
        if M = fail then
            ErrorNoReturn("No preserved quadratic form found for <group>");
        fi;
    fi;

    return M;
end);

# Return a matrix B such that G ^ B preserves the form with matrix <to> for
# every group G preserving the form with matrix <from>; both forms are of kind
# <kind>.
BindGlobal("CM_BaseChangeBetweenForms",
function(kind, from, to, field)
    local d, formByMatrix, fromForm, toForm;

    d := NrRows(from);

    # The Forms package fails in dimension 1, where nonzero forms are similar
    if d = 1 then
        if IsZero(from) <> IsZero(to) then
            ErrorNoReturn("The forms <from> and <to> must be similar");
        fi;
        return IdentityMat(1, field);
    fi;

    if kind in ["S", "O-B"] then
        formByMatrix := BilinearFormByMatrix;
    elif kind = "U" then
        formByMatrix := HermitianFormByMatrix;
    else
        formByMatrix := QuadraticFormByMatrix;
    fi;
    fromForm := formByMatrix(from, field);
    toForm := formByMatrix(to, field);
    if fromForm = toForm then
        return IdentityMat(d, field);
    fi;

    # Symmetric forms in even dimension fall into two similarity classes
    if WittIndex(fromForm) <> WittIndex(toForm) then
        ErrorNoReturn("The forms <from> and <to> must be similar");
    fi;

    return BaseChangeToCanonical(fromForm) ^ -1 * BaseChangeToCanonical(toForm);
end);

# Return a new group G ^ B for the matrix B of CM_BaseChangeBetweenForms, with
# the form <to> stored and B in the component baseChangeMatrix.
BindGlobal("CM_ConjugateBetweenForms",
function(G, kind, from, to, field)
    local B, result;

    B := CM_BaseChangeBetweenForms(kind, from, to, field);
    # an explicit identity, since G may have no generators
    result := GroupByGenerators(List(GeneratorsOfGroup(G), g -> ImmutableMatrix(field, g ^ B)),
                                ImmutableMatrix(field, One(G)));
    UseIsomorphismRelation(G, result);
    result!.baseChangeMatrix := B;

    if kind = "S" then
        SetInvariantBilinearForm(result, rec(matrix := to, baseDomain := field));
    elif kind = "U" then
        SetInvariantSesquilinearForm(result, rec(matrix := to, baseDomain := field));
    elif kind = "O-B" then
        CM_SetInvariantQuadraticFormFromMatrix(result, BilinearToQuadraticForm(to), field);
    else
        CM_SetInvariantQuadraticFormFromMatrix(result, to, field);
    fi;

    return result;
end);

# Return a conjugate of the group G preserving GAP's standard symplectic form,
# given that G preserves the symplectic form with matrix M.
BindGlobal("CM_ConjugateToGAPSymplecticForm",
function(G, M, field)
    local standardForm;

    standardForm := InvariantBilinearForm(Sp(NrRows(M), Size(field))).matrix;
    return CM_ConjugateBetweenForms(G, "S", M, standardForm, field);
end);

# Return a conjugate of the group G preserving GAP's standard unitary form,
# given that G preserves the Hermitian form with matrix M over <field> =
# GF(q ^ 2).
BindGlobal("CM_ConjugateToGAPUnitaryForm",
function(G, M, field)
    local standardForm;

    standardForm := InvariantSesquilinearForm(GU(NrRows(M), RootInt(Size(field), 2))).matrix;
    return CM_ConjugateBetweenForms(G, "U", M, standardForm, field);
end);

# Return a conjugate of the group G preserving GAP's standard orthogonal form
# of sign <epsilon>, given that G preserves the quadratic form with matrix Q.
# In odd characteristic only its bilinear form Q + Q ^ T is used.
BindGlobal("CM_ConjugateToGAPOrthogonalForm",
function(G, epsilon, Q, field)
    local standardGroup, standardForm;

    standardGroup := Omega(epsilon, NrRows(Q), Size(field));
    if IsEvenInt(Size(field)) then
        standardForm := InvariantQuadraticForm(standardGroup).matrix;
        return CM_ConjugateBetweenForms(G, "O-Q", Q, standardForm, field);
    fi;

    standardForm := InvariantBilinearForm(standardGroup).matrix;
    return CM_ConjugateBetweenForms(G, "O-B", Q + TransposedMat(Q), standardForm, field);
end);

# Return a conjugate of <group> preserving the form with matrix <gramMatrix> of
# kind <type>, given that <group> preserves a form of that kind.
InstallGlobalFunction("ConjugateToSesquilinearForm",
function(group, type, gramMatrix, field)
    local formMatrix;

    if not type in ["S", "O-B", "O-Q", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O-B', 'O-Q'");
    fi;

    formMatrix := CM_InvariantFormMatrix(group, type, field);
    return CM_ConjugateBetweenForms(group, type, formMatrix, gramMatrix, field);
end);

# If <group> preserves a sesquilinear form of type <type> (one of "S", "U", "O"
# (in odd dimension), "O+" or "O-" (both in even dimension)), return a group
# conjugate to <group> preserving the standard form of that type.
InstallGlobalFunction("ConjugateToStandardForm",
function(group, type, field)
    local d, Q;

    # sanity checks; <field> is GF(q), or GF(q ^ 2) for type "U"
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
        ErrorNoReturn("If <type> is 'O+', 'O-' or 'O' and the size of <field> is",
                      " even, <d> must be even");
    fi;

    if type = "S" then
        return CM_ConjugateToGAPSymplecticForm(group, CM_InvariantFormMatrix(group, "S", field), field);
    elif type = "U" then
        return CM_ConjugateToGAPUnitaryForm(group, CM_InvariantFormMatrix(group, "U", field), field);
    elif IsEvenInt(Size(field)) then
        Q := CM_InvariantFormMatrix(group, "O-Q", field);
    else
        Q := BilinearToQuadraticForm(CM_InvariantFormMatrix(group, "O-B", field));
    fi;

    return CM_ConjugateToGAPOrthogonalForm(group, Position(["O-", "O", "O+"], type) - 2, Q, field);
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
        ErrorNoReturn("<epsilon> must be -1 or 1 if <d> is even");
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
                xi := PrimitiveRoot(GF(q ^ 2));
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

BindGlobal("CM_ConjugateModule",
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
    local M, formMatrix, q;

    q := Characteristic(F) ^ (DegreeOverPrimeField(F)/2);

    # Return stored sesquilinear form if it exists
    if HasInvariantSesquilinearForm(G) then
        formMatrix := InvariantSesquilinearForm(G).matrix;
    else
        M := GModuleByMats(GeneratorsOfGroup(G), F);
        formMatrix := MTX.InvariantSesquilinearForm(M);
    fi;

    if formMatrix <> fail and formMatrix = HermitianConjugate(formMatrix, q) then
        return ImmutableMatrix(F, formMatrix);
    fi;
    return fail;
end);

# Assuming that the group G acts absolutely irreducibly, try to find a
# bilinear form which is G-invariant or prove that no such form exists.
#
# We use this function instead of PreservedBilinearForms from the Forms package
# since PreservedBilinearForms seems to be buggy and unreliable (see also
# comment above CM_UnitaryForm).
InstallGlobalFunction("CM_BilinearForm",
function(G, F)
    local M, formMatrix, x;

    # Return stored bilinear form if it exists
    if HasInvariantBilinearForm(G) then
        formMatrix := InvariantBilinearForm(G).matrix;
    else
        M := GModuleByMats(GeneratorsOfGroup(G), F);
        formMatrix := MTX.InvariantBilinearForm(M);
        if formMatrix = fail then
            return fail;
        fi;

        # for more consistent results, make the first nonzero entry 1
        x := First(formMatrix[1], y -> not IsZero(y));
        formMatrix := formMatrix * x^-1;
    fi;

    return ImmutableMatrix(F, formMatrix);
end);

InstallGlobalFunction("CM_QuadraticForm",
function(G, F)
    local M, formMatrix;

    if HasInvariantQuadraticForm(G) then
        formMatrix := InvariantQuadraticForm(G).matrix;
    else
        M := GModuleByMats(GeneratorsOfGroup(G), F);
        formMatrix := MTX.InvariantQuadraticForm(M);
        if formMatrix = fail then
            return fail;
        fi;
    fi;
    return ImmutableMatrix(F, formMatrix);
end);

InstallGlobalFunction("CM_ClassicalForms",
function(G, field)
    local M, forms, form, formq, sign, type;
    
    M := GModuleByMats(GeneratorsOfGroup(G), field);
    if not MTX.IsAbsolutelyIrreducible(M) then
        ErrorNoReturn("CM_ClassicalForms: <G> must be absolutely irreducible");
    fi;
    forms := rec();
    forms.formType := "linear";
    forms.bilinearForm := false;
    forms.quadraticForm := false;
    forms.sesquilinearForm := false;

    form := CM_BilinearForm(G, field);
    if form <> fail and form = TransposedMat(form) then
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
    if form <> fail and form = -TransposedMat(form) then
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

# Call CM_ClassicalForms to find a form fixed by the absolutely irreducible
# group G < GL(n, field) and conjugate G via ConjugateToStandardForm.
InstallGlobalFunction("ConjugateToStandardFormAutoType",
function(G, field)
    local forms;

    forms := CM_ClassicalForms(G, field);
    if forms.formType = "unitary" then
        return ConjugateToStandardForm(G, "U", field);
    elif forms.formType = "symplectic" then
        return ConjugateToStandardForm(G, "S", field);
    elif forms.formType = "orthogonalplus" then
        return ConjugateToStandardForm(G, "O+", field);
    elif forms.formType = "orthogonalminus" then
        return ConjugateToStandardForm(G, "O-", field);
    elif forms.formType = "orthogonalcircle" then
        return ConjugateToStandardForm(G, "O", field);
    else
        # forms.formType = "linear"
        return G;
    fi;
end);
