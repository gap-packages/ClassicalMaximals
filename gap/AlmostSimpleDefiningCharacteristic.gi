# TODO
BindGlobal("ConstructDefiningCharacteristicRepresentationOfAlmostSimpleGroup",
function(q)
    # TODO
end);


BindGlobal("ComputeActionGroupOfConstitutionsByDim",
function(G,fld,dim)
    local M, T, MM, A;
    
    M:=GModuleByMats(GeneratorsOfGroup(G), fld);
    T:=TensorProduct(M,M);
    MM:=Filtered(MTX.CompositionFactors(T),c->MTX.Dimension(c) = 8)[1];
    A := Group(MTX.Generators(MM));
    
    return A;
end);


# Construction of group as in Table 5.6 row 4 from [BHR13]
BindGlobal("l3qdim6",
function(q, general)
    local A, G, M, MM, S, T, w;
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
    local A, G, M, MM, S, T, w;
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


BindGlobal("OrthogSL2@",
function(d,q,special,general,normaliser)
    #  /out: construct SL(2,q) in O(d,q) for d odd
    local A,G,M,MM,S,T,i,w;
    Assert(1,IsOddInt(d));
    Assert(1,IsOddInt(q));
    #   construct GL(2,q) as SL(2,q) with extra generator
    w:=PrimitiveElement(GF(q));
    G:=Group(Concatenation(GeneratorsOfGroup(SL(2,q)),[DiagonalMat([w,1])]));
    M:=GModuleByMats(GeneratorsOfGroup(G),GF(q));
    MM:=M;
    for i in [3..d] do
        T:=TensorProductGModule(M,MM);
        MM:=Filtered(MTX.CompositionFactors(T),c->MTX.Dimension(c) = i)[1];
    od;
    A:=Group(MTX.Generators(MM));
    S:=w^(QuoInt((d-1),2))*IdentityMat(d,GF(q));
    A:=GroupByGenerators([GeneratorsOfGroup(A)[1],GeneratorsOfGroup(A)[2],GeneratorsOfGroup(A)[3]*S^(-1)]);
    Assert(1,DeterminantMat(GeneratorsOfGroup(A)[3])= 1 * One(GF(q)));
    # TODO: Translate next line into GAP code
    # Assert(1,SymmetricBilinearForm(A));
    # TODO: Type of ConjugateToStandardForm maybe "O"?
    A:=A^ConjugateToStandardForm(A,"S");
    if normaliser then
        return GroupByGenerators([GeneratorsOfGroup(A)[1],GeneratorsOfGroup(A)[2],GeneratorsOfGroup(A)[3],w*IdentityMat(d,GF(q))]);
    elif general then
        return GroupByGenerators([GeneratorsOfGroup(A)[1],GeneratorsOfGroup(A)[2],GeneratorsOfGroup(A)[3],(-1)*IdentityMat(d,GF(q))]);
    elif special or (GeneratorsOfGroup(A)[3] in Omega(0,d,q)) then
        #  InOmega(A.3,d,q,0) seems to happen for d = 1 or 7 mod 8.
        return A;
    else
        return GroupByGenerators([GeneratorsOfGroup(A)[1],GeneratorsOfGroup(A)[2]]);
    fi;
end);


BindGlobal("SymplecticSL2@",
function(d,q,normaliser)
    #  /out: construct SL(2,q) in Sp(d,q) for d even
    local A,DA,G,M,MM,S,T,form,i,isit,tmat,w,MDA;
    Assert(1,IsEvenInt(d));
    Assert(1,IsOddInt(q));
    #   construct GL(2,q) as SL(2,q) with extra generator
    w:=PrimitiveElement(GF(q));
    G:=GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(2,q)), [DiagonalMat([w,1])]));
    M:=GModuleByMats(GeneratorsOfGroup(G),GF(q));
    MM:=M;
    for i in [3..d] do
        T:=TensorProductGModule(M,MM);
        MM:=Filtered(MTX.CompositionFactors(T),c->MTX.Dimension(c) = i)[1];
    od;
    A:=Group(MTX.Generators(MM));
    S:=w^(QuoInt((d-2),2))*IdentityMat(d,GF(q));
    A:=GroupByGenerators([GeneratorsOfGroup(A)[1],GeneratorsOfGroup(A)[2],GeneratorsOfGroup(A)[3]*S^(-1)]);
    DA:=GroupByGenerators([GeneratorsOfGroup(A)[1],GeneratorsOfGroup(A)[2]]);
    # =v= MULTIASSIGN =v=
    # form:=SymplecticForm@(DA);
    # isit:=form.val1;
    # form:=form.val2;
    # =^= MULTIASSIGN =^=
    # Assert(1,isit);
    # tmat:=TransformForm(form,"symplectic");
    tmat := ConjugateToStandardForm(DA,"S");
    A:=A^tmat;
    if normaliser then
        return A;
    else
        return GroupByGenerators([GeneratorsOfGroup(A)[1],GeneratorsOfGroup(A)[2]]);
    fi;
end);


BindGlobal("l5qdim10@",
function(q,general)
    local A,G,M,MM,S,T,w;
    w:=PrimitiveElement(GF(q));
    # rewritten select statement
    if general then
        G:=GL(5,q);
    else
        G:=SL(5,q);
    fi;
    M:=GModuleByMats(GeneratorsOfGroup(G),GF(q));
    T:=TensorProductGModule(M,M);
    MM:=Filtered(MTX.CompositionFactors(T),c->MTX.Dimension(c) = 10)[1];
    A:=Group(MTX.Generators(MM));
    if not general then
        S:=w^(QuoInt((q-1),Gcd(10,q-1)))*IdentityMat(10,GF(q));
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(A),[S]));
    fi;
    return GroupByGenerators(Concatenation(GeneratorsOfGroup(A),[w*IdentityMat(10,GF(q))]));
end);


BindGlobal("u5qdim10@",
function(q,general,normaliser)
    local A,G,M,MM,S,T,w;
    if normaliser then
        general:=true;
    fi;
    w:=PrimitiveElement(GF(q^2));
    # rewritten select statement
    if general then
        G:=GU(5,q);
    else
        G:=SU(5,q);
    fi;
    M:=GModuleByMats(GeneratorsOfGroup(G),GF(q^2));
    T:=TensorProductGModule(M,M);
    MM:=Filtered(MTX.CompositionFactors(T),c->MTX.Dimension(c) = 10)[1];
    A:=Group(MTX.Generators(MM));
    A:=ConjugateToStandardForm(A, "U");
    if not general then
        S:=(w^(q-1))^(QuoInt((q+1),Gcd(10,q+1)))*IdentityMat(10,GF(q^2));
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(A),[S]));
    fi;
    if not normaliser then
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(A),[w^(q-1)*IdentityMat(10,GF(q^2))]));
    fi;
    return GroupByGenerators(Concatenation(GeneratorsOfGroup(A),[w*IdentityMat(10,GF(q^2))]));
end);


####################################################################################
############################### TODO STEP 1 ########################################
####################################################################################


# TODO: Make sure that the following functions work in GAP.

# Find a replacment in GAP for the following functions:
# * ModToQ
# * IsOverSmallerField

BindGlobal("l2q3dim8@",
function(q,normaliser)
    #  /out:SL(2,q^3).3 <= Sp(8,q);
    local G,M,M1,M2,T,varX,iso,u,w,GG;
    w:=PrimitiveElement(GF(q^3));
    G:=GroupByGenerators(Concatenation(GeneratorsOfGroup(SL(2,q^3)),[DiagonalMat([w,1])]));
    M:=GModuleByMats(G,GF(q^3));
    M1:=ModToQ@(M,q);
    M2:=ModToQ@(M1,q);
    T:=TensorProductGModule(M,TensorProductGModule(M1,M2));
    Assert(1,MTX.IsIrreducible(T));
    u:=PermutationMat((2,3,5)(4,7,6),8,GF(q^3));
    #  induces field automorphism
    varX:= GroupByGenerators(Concatenation(MTX.Generators(T),[u]));
    # =v= MULTIASSIGN =v=
    G:=IsOverSmallerField(varX);
    iso:=G.val1;
    G:=G.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,iso);
    GG := GroupByGenerators([GeneratorsOfGroup(G)[1],GeneratorsOfGroup(G8)[2]]);
    G:=G^TransformForm(SubStructure(G,G.1,G.2));
    if normaliser then
        return G;
    fi;
    return GroupByGenerators([GeneratorsOfGroup(G)[1],GeneratorsOfGroup(G8)[2],GeneratorsOfGroup(G8)[4]]);
end);


BindGlobal("l3qdim8@",
function(q, special, general, normaliser)
    #  /out:SL(3,q)(.3) <= O+(8,q), q mod 3 = 1 or O-(8,q), q mod 3 = 2
    local C,G,G8,M,M8,T,w;
    w:=PrimitiveElement(GF(q));
    G:=GL2@(3,q);
    M:=GModuleByMats(GeneratorsOfGroup(G),GF(q));
    T:=TensorProductGModule(M,M);
    M8:=Filtered(MTX.CompositionFactors(T),c->MTX.Dimension(c) = 8)[1];
    G8:=Group(MTX.Generators(MM));
    G8:=ConjugateToStandardForm(G8, "S");
    if normaliser then
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(G8),[w*IdentityMat(8,GF(q))]));
    elif general and IsOddInt(q) then
        return GroupByGenerators(Concatenation(GeneratorsOfGroup(G8),[-1*IdentityMat(8,GF(q))]));
    elif (special or general) and IsEvenInt(q) then
        return G8;
    elif special or q mod 3=1 then
        return GroupByGenerators([GeneratorsOfGroup(G8)[1],GeneratorsOfGroup(G8)[2],-1*IdentityMat(8,GF(q))]);
    else
        return GroupByGenerators([GeneratorsOfGroup(G8)[1],GeneratorsOfGroup(G8)[2]]);
    fi;
end);


BindGlobal("u3qdim8@",
function(q,special,general,normaliser)
    #  /out:SU(3,q)(.3) <= O+(8,q), q mod 3 = 2 or O-(8,q), q mod 3 = 1
    local C,G,G8,G8q,M,M8,T,isit,w;
    w:=PrimitiveElement(GF(q));
    G:=GU2@(3,q);
    A := ComputeActionGroupOfConstitutionsByDim(G,GF(q),8);
    # =v= MULTIASSIGN =v=
    G8q:=IsOverSmallerField(G8);
    isit:=G8q.val1;
    G8q:=G8q.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    G8q:=G8q^TransformForm(G8q);
    if normaliser then
        return SubStructure(GL(8,q),G8q,#TODO CLOSURE
        ScalarMat(8,w));
    elif general and IsOddInt(q) then
        return SubStructure(GL(8,q),G8q,#TODO CLOSURE
        ScalarMat(8,-1));
    elif (special or general) and IsEvenInt(q) then
        return SubStructure(GL(8,q),G8q);
    elif special or q mod 3=2 then
        return SubStructure(GL(8,q),G8q.1,#TODO CLOSURE
        G8q.2,ScalarMat(8,-1));
    else
        return SubStructure(GL(8,q),G8q.1,#TODO CLOSURE
        G8q.2);
    fi;
end);


BindGlobal("l2q2dim9@",
function(q,special,general,normaliser)
    #  /out:L(2,q^2).2 <= O(9,q);
    local C,G,M,M1,T,varX,form,g3,g4,gg,isit,iso,rt,scal,tform,u,w,z;
    w:=PrimitiveElement(GF(q^2));
    z:=w^(q+1);
    G:=SubStructure(GL(2,q^2),SL(2,q^2),#TODO CLOSURE
        DiagonalMat(GF(q^2),[w,1]));
    M:=GModule(G);
    M1:=ModToQ@(M,q);
    T:=TensorProduct(M,M1);
    Assert(1,IsIrreducible(T));
    u:=PermutationMatrix@(GF(q^2),Tuple([2,3]) #CAST SymmetricGroup(4)
        ) #CAST GL(4,q^2)
        ;
    #  induces field automorphism
    varX:=SubStructure(GL(4,q^2),ActionGroup(T),#TODO CLOSURE
        u);
    # =v= MULTIASSIGN =v=
    G:=IsOverSmallerField(varX);
    iso:=G.val1;
    G:=G.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,iso);
    M:=GModule(G);
    T:=TensorProduct(M,M);
    C:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=9)[1];
    G:=ActionGroup(C);
    G:=G^TransformForm(SubStructure(G,G.1,#TODO CLOSURE
        G.2));
    #  adjust G.3 to fix form and G.4 to have determinant 1
    # =v= MULTIASSIGN =v=
    form:=SymmetricBilinearForm(SubStructure(G,G.1,#TODO CLOSURE
        G.2));
    isit:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    tform:=G.3*form*TransposedMat(G.3);
    scal:=form[1][9]/tform[1][9];
    # =v= MULTIASSIGN =v=
    rt:=IsPower(scal,2);
    isit:=rt.val1;
    rt:=rt.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    g3:=G.3*ScalarMat(9,rt);
    # rewritten select statement
    if DeterminantMat(g3)=1 then
        g3:=g3;
    else
        g3:=-g3;
    fi;
    # rewritten select statement
    if DeterminantMat(G.4)=1 then
        g4:=G.4;
    else
        g4:=-G.4;
    fi;
    G:=SubStructure(GL(9,q),G.1,#TODO CLOSURE
        G.2,g3,g4);
    if normaliser then
        return SubStructure(GL(9,q),G,#TODO CLOSURE
        ScalarMat(9,z));
    elif general then
        return SubStructure(GL(9,q),G,#TODO CLOSURE
        ScalarMat(9,-1));
    elif special then
        return G;
    else
        # rewritten select statement
        if InOmega@(g3,9,q,0) then
            gg:=g3;
        else
            # rewritten select statement
            if InOmega@(g4,9,q,0) then
                gg:=g4;
            else
                gg:=g3*g4;
            fi;
        fi;
        return (SubStructure(G,G.1,#TODO CLOSURE
        G.2,gg));
    fi;
end);


BindGlobal("l3q2dim9l@",
function(q,general)
    #  /out:(3.)L(3,q^2)(.3).2 <= L(9,q)
    local G,M,M1,T,varX,g4,iso,u,w,z;
    w:=PrimitiveElement(GF(q^2));
    z:=w^(q+1);
    G:=SubStructure(GL(3,q^2),SL(3,q^2),#TODO CLOSURE
        DiagonalMat(GF(q^2),[w,1,1]));
    M:=GModule(G);
    M1:=ModToQ@(M,q);
    T:=TensorProduct(M,M1);
    Assert(1,IsIrreducible(T));
    u:=PermutationMatrix@(GF(q^2),(2,4)(3,7)(6,8) #CAST SymmetricGroup(9)
        ) #CAST GL(9,q^2)
        ;
    #  induces field automorphism
    varX:=SubStructure(GL(9,q^2),ActionGroup(T),#TODO CLOSURE
        u);
    # =v= MULTIASSIGN =v=
    G:=IsOverSmallerField(varX);
    iso:=G.val1;
    G:=G.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,iso);
    #  adjust G.4 to have determinant 1
    # rewritten select statement
    if DeterminantMat(G.4)=1 then
        g4:=G.4;
    else
        g4:=-G.4;
    fi;
    G:=SubStructure(GL(9,q),G.1,#TODO CLOSURE
        G.2,G.3,g4);
    if general then
        return SubStructure(GL(9,q),G,#TODO CLOSURE
        ScalarMat(9,z));
    else
        #  get power of G.3 with determinant 1
        return (SubStructure(G,G.1,#TODO CLOSURE
        G.2,G.3^Order(DeterminantMat(G.3)),G.4));
    fi;
end);


BindGlobal("l3q2dim9u@",
function(q,general,normaliser)
    #  /out:(3.)L(3,q^2)(.3).2 <= L(9,q)
    local G,M,M1,T,g4,u,w,z;
    w:=PrimitiveElement(GF(q^2));
    z:=w^(q-1);
    G:=SubStructure(GL(3,q^2),SL(3,q^2),#TODO CLOSURE
        DiagonalMat(GF(q^2),[w,1,1]));
    M:=GModule(G);
    M1:=ModToQ@(M,q);
    T:=TensorProduct(Dual(M),M1);
    Assert(1,IsIrreducible(T));
    u:=PermutationMatrix@(GF(q^2),(2,4)(3,7)(6,8) #CAST SymmetricGroup(9)
        ) #CAST GL(9,q^2)
        ;
    #  induces field automorphism
    G:=SubStructure(GL(9,q^2),ActionGroup(T),#TODO CLOSURE
        u);
    G:=G^TransformForm(SubStructure(G,G.1,#TODO CLOSURE
        G.2));
    #  adjust G.4 to have determinant 1
    # rewritten select statement
    if DeterminantMat(G.4)=1 then
        g4:=G.4;
    else
        g4:=-G.4;
    fi;
    G:=SubStructure(GL(9,q^2),G.1,#TODO CLOSURE
        G.2,G.3,g4);
    if normaliser then
        return SubStructure(GL(9,q^2),G,#TODO CLOSURE
        ScalarMat(9,w));
    elif general then
        return SubStructure(GL(9,q^2),G,#TODO CLOSURE
        ScalarMat(9,z));
        #  get power of G.3 with determinant 1
    else
        return (SubStructure(G,G.1,#TODO CLOSURE
        G.2,G.3^Order(DeterminantMat(G.3)),G.4));
    fi;
end);


BindGlobal("l3qdim10@",
function(q,general)
    local A,G,M,MM,S,T,g3,isit,o,rt,tp,w;
    Assert(1,CollectedFactors(q)[1][1] >= 5);
    w:=PrimitiveElement(GF(q));
    G:=SubStructure(GL(3,q),SL(3,q),#TODO CLOSURE
        DiagonalMat(GF(q),[w,1,1]));
    M:=GModule(G);
    T:=TensorPower(M,3);
    MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
    G:=ActionGroup(MM);
    if general then
        return SubStructure(GL(10,q),G,#TODO CLOSURE
        ScalarMat(10,w));
    fi;
    #  get intersection with SL
    o:=Order(DeterminantMat(G.3));
    tp:=3^Valuation(o,3);
    g3:=G.3^(QuoInt(o,tp));
    # =v= MULTIASSIGN =v=
    rt:=IsPower(DeterminantMat(g3),10);
    isit:=rt.val1;
    rt:=rt.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    g3:=g3*ScalarMat(10,rt^-1);
    S:=ScalarMat(10,w^(QuoInt((q-1),Gcd(10,q-1))));
    return SubStructure(GL(10,q),G.1,#TODO CLOSURE
        G.2,g3,S);
end);


BindGlobal("u3qdim10@",
function(q,general,normaliser)
    local A,G,M,MM,S,T,g3,isit,o,rt,tp,w;
    Assert(1,CollectedFactors(q)[1][1] >= 5);
    if normaliser then
        general:=true;
    fi;
    w:=PrimitiveElement(GF(q^2));
    G:=SubStructure(GL(3,q^2),SU(3,q),#TODO CLOSURE
        GU(3,q).1);
    M:=GModule(G);
    T:=TensorPower(M,3);
    MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
    A:=ActionGroup(MM);
    G:=A^TransformForm(A);
    if normaliser then
        return SubStructure(GL(10,q^2),G,#TODO CLOSURE
        ScalarMat(10,w));
    fi;
    if general then
        return SubStructure(GL(10,q^2),G,#TODO CLOSURE
        ScalarMat(10,w^(q-1)));
    fi;
    #  get intersection with SU
    o:=Order(DeterminantMat(G.3));
    tp:=3^Valuation(o,3);
    g3:=G.3^(QuoInt(o,tp));
    # =v= MULTIASSIGN =v=
    rt:=IsPower(DeterminantMat(g3),10*(q-1));
    isit:=rt.val1;
    rt:=rt.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    g3:=g3*ScalarMat(10,rt^-(q-1));
    S:=ScalarMat(10,(w^(q-1))^(QuoInt((q+1),Gcd(10,q+1))));
    return SubStructure(GL(10,q^2),G.1,#TODO CLOSURE
        G.2,g3,S);
end);


BindGlobal("l4qdim10@",
function(q,general)
    local A,G,M,MM,S,T,g3,isit,o,rt,tp,w;
    Assert(1,CollectedFactors(q)[1][1] >= 3);
    w:=PrimitiveElement(GF(q));
    G:=SubStructure(GL(4,q),SL(4,q),#TODO CLOSURE
        DiagonalMat(GF(q),[w,1,1,1]));
    M:=GModule(G);
    T:=TensorPower(M,2);
    MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
    G:=ActionGroup(MM);
    if general then
        return SubStructure(GL(10,q),G,#TODO CLOSURE
        ScalarMat(10,w));
    fi;
    #  get intersection with SL
    o:=Order(DeterminantMat(G.3));
    tp:=2^Valuation(o,2);
    g3:=G.3^(QuoInt(2*o,tp));
    # =v= MULTIASSIGN =v=
    rt:=IsPower(DeterminantMat(g3),10);
    isit:=rt.val1;
    rt:=rt.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    g3:=g3*ScalarMat(10,rt^-1);
    S:=ScalarMat(10,w^(QuoInt((q-1),Gcd(10,q-1))));
    return SubStructure(GL(10,q),G.1,#TODO CLOSURE
        G.2,g3,S);
end);


BindGlobal("u4qdim10@",
function(q,general,normaliser)
    local A,G,M,MM,S,T,g3,isit,o,rt,tp,w;
    Assert(1,CollectedFactors(q)[1][1] >= 3);
    if normaliser then
        general:=true;
    fi;
    w:=PrimitiveElement(GF(q^2));
    G:=SubStructure(GL(4,q^2),SU(4,q),#TODO CLOSURE
        GU(4,q).1);
    M:=GModule(G);
    T:=TensorPower(M,2);
    MM:=Filtered(Constituents(T),c->DimensionOfMatrixGroup(c)=10)[1];
    A:=ActionGroup(MM);
    G:=A^TransformForm(A);
    if normaliser then
        return SubStructure(GL(10,q^2),G,#TODO CLOSURE
        ScalarMat(10,w));
    fi;
    if general then
        return SubStructure(GL(10,q^2),G,#TODO CLOSURE
        ScalarMat(10,w^(q-1)));
    fi;
    #  get intersection with SU
    o:=Order(DeterminantMat(G.3));
    tp:=2^Valuation(o,2);
    g3:=G.3^(QuoInt(2*o,tp));
    # =v= MULTIASSIGN =v=
    rt:=IsPower(DeterminantMat(g3),10*(q-1));
    isit:=rt.val1;
    rt:=rt.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    g3:=g3*ScalarMat(10,rt^-(q-1));
    S:=ScalarMat(10,(w^(q-1))^(QuoInt((q+1),Gcd(10,q+1))));
    return SubStructure(GL(10,q^2),G.1,#TODO CLOSURE
        G.2,g3,S);
end);


BindGlobal("sp4qdim10@",
function(q,special,general,normaliser)
    #  /out:Sp4q <= O^+(10,q) (q=1 mod 4) or O^-(10,q) (q=3 mod 4)
    local C,G,M,M10,form,g3,isit,rt,scal,sign,tform,w;
    Assert(1,IsOddInt(q));
    w:=PrimitiveElement(GF(q));
    G:=SubStructure(GL(4,q),SP(4,q),#TODO CLOSURE
        NormSpMinusSp@(4,q));
    M:=GModule(G);
    C:=Constituents(TensorProduct(M,M));
    M10:=Filtered(C,c->DimensionOfMatrixGroup(c)=10)[1];
    G:=ActionGroup(M10);
    G:=G^TransformForm(SubStructure(G,G.1,#TODO CLOSURE
        G.2));
    # =v= MULTIASSIGN =v=
    form:=SymmetricBilinearForm(SubStructure(G,G.1,#TODO CLOSURE
        G.2));
    isit:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    tform:=G.3*form*TransposedMat(G.3);
    scal:=form[1][10]/tform[1][10];
    # =v= MULTIASSIGN =v=
    rt:=IsPower(scal,2);
    isit:=rt.val1;
    rt:=rt.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isit);
    g3:=G.3*ScalarMat(10,rt);
    G:=SubStructure(GL(10,q),G.1,#TODO CLOSURE
        G.2,g3);
    # rewritten select statement
    if q mod 4=1 then
        sign:=1;
    else
        sign:=-1;
    fi;
    Assert(1,DeterminantMat(g3)=1 and not InOmega@(g3,10,q,sign));
    if normaliser then
        return SubStructure(GL(10,q),G,#TODO CLOSURE
        ScalarMat(10,w));
    elif special or general then
        return SubStructure(GL(10,q),G,#TODO CLOSURE
        ScalarMat(10,-1));
    else
        return SubStructure(GL(10,q),G.1,#TODO CLOSURE
        G.2,ScalarMat(10,-1));
    fi;
end);
