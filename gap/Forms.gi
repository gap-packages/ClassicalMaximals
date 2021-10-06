# If <type> = "S" or type = "O" then <group> must have the attribute
# InvariantBilinearForm.
# Also, one need to ensure that the attribute DefaultFieldOfMatrixGroup is set
# correctly for <group>; this can be done, for example, by making the
# generators used during construction of the group immutable matrices over the
# appropriate field.
InstallGlobalFunction("ChangeFixedSesquilinearForm",
function(group, type, gramMatrix)
    local gapForm, newForm, gapToCanonical, canonicalToNew, field, formMatrix,
        result;
    if not type in ["S", "O", "U"] then
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O', but <type> = ",
                      type);
    fi;
    field := DefaultFieldOfMatrixGroup(group);
    if type = "S" or type = "O" then
        gapForm := BilinearFormByMatrix(InvariantBilinearForm(group).matrix, 
                                        field);
        newForm := BilinearFormByMatrix(gramMatrix, field);
    else
        if HasInvariantSesquilinearForm(group) then
            gapForm := HermitianFormByMatrix(InvariantSesquilinearForm(group).matrix,
                                             field);
        else    
            formMatrix := UnitaryForm(group);
            if formMatrix = fail then
                Error("No preserved unitary form found for <group>");
            fi;
            gapForm := HermitianFormByMatrix(formMatrix, field);
        fi;
        newForm := HermitianFormByMatrix(gramMatrix, field);
    fi;
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
    result := MatrixGroup(canonicalToNew(gapToCanonical(GeneratorsOfGroup(group))), field);
    if HasSize(group) then
        SetSize(result, Size(group));
    fi;
    return result;
end);

# Can only deal with sesquilinear forms, not with quadratic forms as of yet.
# If <type> is one of "S", "O+", "O-" or "O" then <group> must have the
# attribute InvariantBilinearForm.
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
        ErrorNoReturn("<type> must be one of 'S', 'U', 'O+', 'O-', 'O'",
                      " but <type> =", type);
    fi;
    F := DefaultFieldOfMatrixGroup(group);
    d := DimensionOfMatrixGroup(group);
    if type = "O" and IsEvenInt(d) then
        ErrorNoReturn("<type> cannot be 'O' if the dimension of <group> is even");
    elif type in ["O+", "O-"] and IsOddInt(d) then
        ErrorNoReturn("<type> cannot be 'O+' or 'O-' if the dimension of",
                      " <group> is odd");
    fi;
    if type in ["S", "O", "O+", "O-"] then
        q := Size(F);
    else
        if IsSquareInt(Size(F)) then
            q := RootInt(Size(F));
        else
            ErrorNoReturn("<group> must have a base field of square order", 
                          " when <type> = 'U'");
        fi;
    fi;
    if type in ["O", "O+", "O-"] and IsEvenInt(q) then
        ErrorNoReturn("ConjugateToGAPForm cannot deal with orthogonal groups in",
                      " even characteristic yet");
    fi;
    
    # get standard GAP form
    if type = "S" then
        gapForm := InvariantBilinearForm(Sp(d, q)).matrix;
    elif type = "U" then
        gapForm := InvariantSesquilinearForm(GU(d, q)).matrix;
    elif type = "O" then
        gapForm := InvariantBilinearForm(GO(d, q)).matrix;
    elif type = "O+" then
        gapForm := InvariantBilinearForm(GO(1, d, q)).matrix;
    elif type = "O-" then
        gapForm := InvariantBilinearForm(GO(-1, d, q)).matrix;
    fi;

    if type in ["O", "O+", "O-"] then
        broadType := "O";
    else
        broadType := type;
    fi;

    return ChangeFixedSesquilinearForm(group, broadType, gapForm);
end);


ConjugateModule := function(M, q)
  return GModuleByMats(List(MTX.Generators(M), A -> ApplyFunctionToEntries(A, x -> x ^ q)), 
                       MTX.Field(M));
end;

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
        return fail;
    fi;
    q := RootInt(Size(F));

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
                row := First([1..NrRows(formMatrix)], x -> not IsZero(formMatrix[x]));
                col := First([1..NrCols(formMatrix)], x -> not IsZero(formMatrix[row][x]));
                if not IsZero(formMatrix[col, row]) then
                    # this must be 1 for formMatrix to be hermitian
                    x := formMatrix[row, col] * formMatrix[col, row] ^ (-q);
                    # multiplying formMatrix by scalar will ensure that x = 1, i.e. that
                    # formMatrix is hermitian
                    scalar := RootFFE(x, q - 1);
                fi;

                if IsZero(formMatrix[col, row]) or scalar = fail then
                    if not MTX.IsAbsolutelyIrreducible(M) then
                        Error("UnitaryForm failed - group is not absolutely irreducible");
                    fi;
                    continue;
                fi;

                # make formMatrix hermitian
                formMatrix := scalar * formMatrix;
            fi;

            if formMatrix <> HermitianConjugate(formMatrix, q) and not MTX.IsAbsolutelyIrreducible(M) then
                Error("UnitaryForm failed - group is not absolutely irreducible");
            fi;

            return formMatrix;
        fi;
    od;

    return fail;
end);
