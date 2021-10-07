# TODO
BindGlobal("ConstructDefiningCharacteristicRepresentationOfAlmostSimpleGroup",
function(q)
    # TODO
end);


# Construction of group as in Table 5.6 row 4 from [BHR13]
BindGlobal("l3qdim6",
function(q, general)
    local A, G, M, MM, S, T, general, w;
    Assert(1,IsOddInt(q));
    w := PrimitiveElement(GF(q));
    # rewritten select statement
    if general then
        G := GL(3,q);
    else
        G := SL(3,q);
    fi;
    M := GModuleByMats(GeneratorsOfGroup(G),GF(q));
    T := TensorProductGModule(M,M);
    MM := Filtered(MTX.CompositionFactors(T),c->MTX.Dimension(c)=6)[1];
    if not general then
        S := w^(QuoInt((q-1),Gcd(6,q-1)))*IdentityMat(6,GF(q));
    else
        S := w*IdentityMat(6,GF(q));
    fi;
    return Group(Concatenation(MTX.Generators(MM),[S]));
end);

# Construction of group as in Table 5.6 row 5 from [BHR13]
BindGlobal("u3qdim6",
function(q, general, normaliser)
    local A, G, M, MM, S, T, general, normaliser, w;
    Assert(1,IsOddInt(q));
    if normaliser then
        general := true;
    fi;
    w := PrimitiveElement(GF(q^2));
    # rewritten select statement
    if general then
        G := GU(3,q);
    else
        G := SU(3,q);
    fi;
    M := GModuleByMats(GeneratorsOfGroup(G),GF(q^2));
    T := TensorProductGModule(M,M);
    MM := Filtered(MTX.CompositionFactors(T),c->MTX.Dimension(c) = 6)[1];
    A := Group(MTX.Generators(MM));
    # change back fixed form into standard GAP form Antidiag(1, ..., 1)
    # SetInvariantSesquilinearForm(A, rec(matrix := Unitary(A)));
    A := ConjugateToStandardForm(A, "U");
    if not general then
        S := (w^(q-1))^(QuoInt((q+1),Gcd(6,q+1)))*IdentityMat(6,GF(q^2));
    elif not normaliser then
        S := w^(q-1)*IdentityMat(6,GF(q^2));
    else 
        S := w*IdentityMat(6,GF(q^2));
    fi;
    
    return Group(Concatenation(GeneratorsOfGroup(A),[S]));
end);
