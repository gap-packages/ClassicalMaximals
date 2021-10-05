# Construction of group as in Table 5.6 row 4 from [BHR13]
BindGlobal("l3qdim6",
function(q)
    local A, G, M, MM, S, T, general, w;
    general := ValueOption("general");
    if general = fail then
        general := false;
    fi;
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
