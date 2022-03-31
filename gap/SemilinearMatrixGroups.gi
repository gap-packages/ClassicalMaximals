# Return a subgroup of <M>GL(s, q)</M> isomorphic to the subgroup of
# <M>\Gamma L(1, q ^ s)</M> consisting of all <C>GF(q)</C>-linear and 
# <C>GF(q ^ s)</C>-semilinear transformations of the vector space 
# <M>F'^1</M> over the field <C>F' := GF(q ^ s)</C>. 
# See <Ref Func="GammaLMeetSL"/> for further details.
#
# Construction as in Lemma 6.1 of [HR05]
# Note that in [HR05], it is falsely claimed that the group constructed is
# isomorphic to GammaL(1, q ^ s) when in fact it is only isomorphic to the
# subgroup of GammaL(1, q ^ s) consisting of all GF(q)-linear transformations.
BindGlobal("MatricesInducingGaloisGroupOfGFQToSOverGFQ",
function(s, q)
    local F, primitivePolynomial, A, x, xq, B, row, i;
    F := GF(q);
    # Let w be a primitive element of GF(q ^ s) over GF(q).
    # A acts on the standard basis in the same way as w acts by multiplication
    # on the GF(q)-basis {1, w, w ^ 2, ...} of GF(q ^ s). (Note that A is a
    # Singer cycle, i.e. has order q ^ s - 1.)
    primitivePolynomial := MinimalPolynomial(F, Z(q ^ s));
    A := TransposedMat(CompanionMat(primitivePolynomial));
    # B acts on the standard basis in the same way as the Frobenius acts on the
    # basis {1, w, w ^ 2, ...} of GF(q ^ s) over GF(q), where w is as above.
    x := IndeterminateOfUnivariateRationalFunction(primitivePolynomial);
    xq := PowerMod(x, q, primitivePolynomial);
    B := [];
    for i in [0 .. s - 1] do
        row := List(CoefficientsOfUnivariatePolynomial(PowerMod(xq,
                                                           i,
                                                           primitivePolynomial)));
        Append(row, ListWithIdenticalEntries(s - Length(row), Zero(F)));
        Add(B, row);
    od;
    return rec(A := A, B := B);
end);

# Return a block matrix where the block in place (i, j) is A ^ k if and only if
# the entry M[i, j] is omega ^ k (if M[i, j] = 0 then the corresponding block
# is zero as well).
# This is the function Theta(...) from [HR05] defined on page 61 before Lemma 6.2.
BindGlobal("MapGammaLToGL",
function(M, A, omega)
    local result, i, j, exponent, dimensionOfA, omegainv;

    if not NumberRows(A) = NumberColumns(A) then
        ErrorNoReturn("<A> must be a square matrix");
    fi;

    dimensionOfA := NumberRows(A);
    result := NullMat(NumberRows(M) * dimensionOfA, 
                      NumberColumns(M) * dimensionOfA, 
                      DefaultFieldOfMatrix(A));

    omegainv := omega^-1;
    for i in [1..NumberRows(M)] do
        for j in [1..NumberColumns(M)] do
            if not IsZero(M[i, j]) then
                # Hack: for large fields, LogFFE is extremely inefficient; but
                # for the matrices we consider (generators of SL or Sp), all
                # entries really are either 0, 1, omega or omega^-1. All but
                # the last one are handled efficiently by LogFFE. So we deal
                # with the remaining case here.
                if M[i, j] = omegainv then
                    exponent := -1;
                else
                    exponent := LogFFE(M[i, j], omega);
                fi;
                result{[(i - 1) * dimensionOfA + 1..i * dimensionOfA]}
                      {[(j - 1) * dimensionOfA + 1..j * dimensionOfA]} 
                          := A ^ exponent;
            fi;
        od;
    od;

    return result;
end);

# Variant of MapGammaLToGL: here M is assumed to be a matrix whose entries are
# univariate rational functions, which we evaluate at A.
BindGlobal("MapGammaLToGLRatFun",
function(M, A)
    local result, i, j, dimensionOfA;

    if not NumberRows(A) = NumberColumns(A) then
        ErrorNoReturn("<A> must be a square matrix");
    fi;

    dimensionOfA := NumberRows(A);
    result := NullMat(NumberRows(M) * dimensionOfA,
                      NumberColumns(M) * dimensionOfA,
                      DefaultFieldOfMatrix(A));

    for i in [1..NumberRows(M)] do
        for j in [1..NumberColumns(M)] do
            if not IsZero(M[i, j]) then
                result{[(i - 1) * dimensionOfA + 1..i * dimensionOfA]}
                      {[(j - 1) * dimensionOfA + 1..j * dimensionOfA]}
                          := Value(M[i, j], A);
            fi;
        od;
    od;

    return result;
end);

# Return the subgroup of <M>SL(n, q)</M> induced by the group of all 
# <C>GF(q)</C>-linear and <C>GF(q ^ s)</C>-semilinear
# transformations of the vector space <M>F'^m</M> over the field 
# <C>F' := GF(q ^ s)</C>, where <M>m := n / s</M>. (More precisely, there is
# an isomorphism of <M>F</M>-vector spaces, where <C>F := GF(q)</C>, between
# <M>F'</M> and <M>F ^ s</M>, which in turn induces an <M>F</M>-vector space
# isomorphism between <M>F'^m</M> and <M>F^n</M> and consequently an embedding
# of the subgroup of <M>\Gamma L(m, q ^ s)</M> consisting of all
# <C>GF(q)</C>-linear transformations of <M>F'^m</M> into <M>GL(n, q)</M>; 
# the intersection of the image of this embedding with <M>SL(n, q)</M> is a 
# subgroup of <M>SL(n, q)</M>.) Note that this means <A>s</A> must be a divisor 
# of <A>n</A>. We further demand that <A>s</A> be a prime number, i.e. <M>F'</M> 
# is a prime extension of <M>F</M>.
# Construction as in Proposition 6.3 of [HR05]
BindGlobal("GammaLMeetSL",
function(n, q, s)
    local F, As, Bs, Cs, Fs, m, gammaL1, zeta, AandB, C, D, DBlock, ZBlock, i,
    range, size;
    if n mod s <> 0 or not IsPrime(s) then
        ErrorNoReturn("<s> must be prime and a divisor of <n>");
    fi;
    F := GF(q);
    gammaL1 := MatricesInducingGaloisGroupOfGFQToSOverGFQ(s, q);
    # Let w be a primitive element of GF(q ^ s) over GF(q). Since As is the
    # companion matrix of the minimal polynomial of w over GF(q), its
    # determinant is (-1) ^ s times the constant term of said minimal
    # polynomial. By Vieta, this constant term is (-1) ^ s * the product of
    # all Galois conjugates of w. Hence, det(As) = w ^ ((q ^ s - 1) / (q - 1)).
    As := gammaL1.A;
    # By Lemma 6.2 det(Bs) = (-1) ^ (s - 1).
    Bs := gammaL1.B;
    # det(Cs) = det(As) ^ (q - 1) = w ^ (q ^ s - 1) = 1.
    Cs := As ^ (q - 1);
    m := QuoInt(n, s);

    # Size according to Proposition 6.3 of [HR05]
    size := SizeSL(n / s, q ^ s) * (q ^ s - 1) / (q - 1) * s;

    if m = 1 then
        if n mod 2 = 1 then
            return MatrixGroupWithSize(F, [Bs, Cs], size);
        elif q mod 2 = 1 then
            Fs := (As ^ QuoInt(q - 1, 2)) * Bs;
            return MatrixGroupWithSize(F, [Cs, Fs], size);
        # n = s = 2 and q even
        else
            # In characteristic 2 we have det(Bs) = -1 = 1.
            return MatrixGroupWithSize(F, [Bs, Cs], size);
        fi;
    fi;

    zeta := PrimitiveRoot(GF(q ^ s));
    AandB := List(GeneratorsOfGroup(SL(m, q ^ s)), g -> MapGammaLToGL(g, As, zeta));
    C := IdentityMat(n, F);
    C{[1..s]}{[1..s]} := Cs;
    D := IdentityMat(n, F);
    # The determinant of D might be -1. In these cases, adjust D.
    if s = 2 and IsOddInt(m) and IsOddInt(q) then
        ZBlock := As ^ QuoInt(q - 1, 2);
        DBlock := ZBlock * Bs;
    else
        DBlock := Bs;
    fi;
    for i in [0..m - 1] do
        range := [i * s + 1..(i + 1) * s];
        D{range}{range} := DBlock;
    od;

    return MatrixGroupWithSize(F, Concatenation(AandB, [C, D]), size);
end);

# For a sesquilinear form beta on the vector space GF(q ^ s) ^ (d / s) given 
# by the Gram matrix <form>, we can interpret any u, v in GF(q) ^ d as elements of 
# GF(q ^ s) ^ (d / s) via the standard basis. Taking the trace of beta(u, v)
# yields a sesquilinear form on the vector space GF(q) ^ d.
#
# Takes a unitary form and returns a unitary form if <type> = "U-U"; takes a
# unitary form and returns a symplectic form if <type> = "U-S"; takes a
# symplectic form and returns a symplectic form if <type> = "S-S". 
BindGlobal("TakeTraceOfSesquilinearForm",
function(form, q, s, type)
    local F, d, newForm, B, rootOfq, i, j, eiOverGFqsEntry, eiOverGFqsIndex,
    ejOverGFqsEntry, ejOverGFqsIndex, exp, valueOfForm;

    if not type in ["S-S", "U-S", "U-U"] then
        ErrorNoReturn("<type> must be one of 'S-S', 'U-S' or 'U-U'");
    fi;
    if type = "U-U" and not IsInt(Sqrt(q)) then
        ErrorNoReturn("<q> must be a square if <type> = 'U-U'");
    fi;
    if type = "U-S" and not s = 2 then
        ErrorNoReturn("<s> must be two if <type> = 'U-S'");
    fi;

    F := GF(q);
    d := s * Size(form);
    newForm := NullMat(d, d, F);
    B := CanonicalBasis(AsField(F, GF(q ^ s)));

    if type = "U-U" then
        rootOfq := Sqrt(q);
    fi;

    if type = "S-S" then
        exp := 1;
    elif type = "U-S" then
        exp := q;
    else
        exp := rootOfq ^ s;
    fi;

    for i in [1..d] do
        # The basis vector ei of GF(q) ^ d corresponds to a vector in 
        # GF(q ^ s) ^ (d / s) with the entry eiOverGFqsEntry in the 
        # eiOverGFqsIndex-th component.
        eiOverGFqsEntry := B[(i - 1) mod s + 1];
        eiOverGFqsIndex := QuoInt(i - 1, s) + 1;

        for j in [1..i] do
            ejOverGFqsEntry := B[(j - 1) mod s + 1];
            ejOverGFqsIndex := QuoInt(j - 1, s) + 1;

            valueOfForm := eiOverGFqsEntry * form[eiOverGFqsIndex, ejOverGFqsIndex] 
                                           * ejOverGFqsEntry ^ exp;
            newForm[i, j] := TraceOverFiniteField(valueOfForm, q, s);

        od;
    od;

    # If type = "S-S" or type = "U-S", newForm must be an anti-symmetric matrix; 
    # likewise, if type = "U-U", newForm must be a hermitian matrix
    if type = "S-S" or type = "U-S" then
        newForm := newForm - TransposedMat(newForm);
    else
        newForm := newForm + HermitianConjugate(newForm, rootOfq) 
                           - DiagonalMat(DiagonalOfMat(newForm));
    fi;

    return newForm;
end);

# Return generating matrices for GU(n,q) but with a twist: the argument `z`
# can be set either to a primitive root of GF(q^2); or to an indeterminate. In
# the former case, regular generators are returned. In the latter case, the
# result are matrices whose entries are rational functions. This is useful in
# combination with "MapGammaLToGLRatFun".
#
# This function is adapted from the code of the GAP library function
# "GeneralUnitaryGroupCons", but with minor modifications and cleanup; in a
# few cases slightly different generators may be returned, but the generated
# groups are equal.
BindGlobal( "GeneralUnitaryGroupGens",
function( n, q, z )
    local g, i, e, f, o, mat1, mat2;

    f:= DefaultField(z);
    o:= z^0;

    # Construct the generators.
    if n = 1 then
        return [ [ [ z ^ (q-1) ] ] ];
    fi;

    mat1:= IdentityMat( n, f );
    mat2:= NullMat( n, n, f );

    if n = 2 then

      # We use the isomorphism of 'SU(2,q)' and 'SL(2,q)':
      # 'e' is mapped to '-e' under the Frobenius mapping.
      if q mod 2 = 1 then e:= z^( (q+1)/2 ); else e:= o; fi;
      if q = 2 then
        mat1[1,1]:= z;
        mat1[2,2]:= z;
        mat1[1,2]:= z;
        mat2[1,2]:= o;
        mat2[2,1]:= o;
      else
        mat1[1,1]:= z;
        mat1[2,2]:= z^-q;
        mat2[1,1]:= -o;
        mat2[1,2]:= e;
        mat2[2,1]:= -e^-1;
      fi;

    elif n mod 2 = 0 then

      mat1[1,1]:= z;
      mat1[n,n]:= z^-q;

      if q mod 2 = 1 then e:= z^( (q+1)/2 ); else e:= o; fi;
      for i in [ 2 .. n/2 ]     do mat2[ i, i-1 ]:= o; od;
      for i in [ n/2+1 .. n-1 ] do mat2[ i, i+1 ]:= o; od;
      mat2[ 1, 1 ]:= o;
      mat2[1,n/2+1]:= e;
      mat2[n-1,n/2]:= e^-1;
      mat2[n, n/2 ]:= -e^-1;

    else

      mat1[(n-1)/2  ,(n-1)/2  ]:= z;
      mat1[(n-1)/2+2,(n-1)/2+2]:= z^-q;

      for i in [ 1 .. (n-1)/2-1 ] do mat2[ i, i+1 ]:= o; od;
      for i in [ (n-1)/2+3 .. n ] do mat2[ i, i-1 ]:= o; od;
      mat2[(n-1)/2,    1    ]:=  -(1+z^q/z)^-1;
      mat2[(n-1)/2,(n-1)/2+1]:= -o;
      mat2[(n-1)/2,    n    ]:=  o;
      mat2[(n-1)/2+1,  1    ]:= -o;
      mat2[(n-1)/2+1,(n-1)/2+1]:= -o;
      mat2[(n-1)/2+2,  1  ]:=  o;
    fi;

    return [ mat1, mat2 ];
end );


# Return generating matrices for SU(n,q) but with a twist: the argument `z`
# can be set either to a primitive root of GF(q^2); or to an indeterminate. In
# the former case, regular generators are returned. In the latter case, the
# result are matrices whose entries are rational functions. This is useful in
# combination with "MapGammaLToGLRatFun".
#
# This function is adapted from the code of the GAP library function
# "SpecialUnitaryGroupCons", but with minor modifications and cleanup; in a
# few cases slightly different generators may be returned, but the generated
# groups are equal.
BindGlobal( "SpecialUnitaryGroupGens",
function( n, q, z )
    local g, i, e, f, o, mat1, mat2;

    f:= DefaultField(z);
    o:= z^0;

    # Construct the generators.
    if n = 1 then
        return [ IdentityMat( n, f ) ];
    fi;

    mat1:= IdentityMat( n, f );
    mat2:= NullMat( n, n, f );

    if n = 2 then

      # We use the isomorphism of 'SU(2,q)' and 'SL(2,q)':
      # 'e' is mapped to '-e' under the Frobenius mapping.
      if q mod 2 = 1 then e:= z^( (q+1)/2 ); else e:= o; fi;
      if q <= 3 then
        mat1[1,2]:= e;
        mat2[1,2]:= e;
        mat2[2,1]:= -e^-1;
      else
        mat1[1,1]:= z^(q+1);
        mat1[2,2]:= z^(-q-1);
        mat2[1,1]:= -o;
        mat2[1,2]:= e;
        mat2[2,1]:= -e^-1;
      fi;

    elif n mod 2 = 0 then

      mat1[1,1]:= z;
      mat1[n,n]:= z^-q;
      mat1[2,2]:= z^-1;
      mat1[n-1,n-1]:= z^q;

      if q mod 2 = 1 then e:= z^( (q+1)/2 ); else e:= o; fi;
      for i in [ 2 .. n/2 ]     do mat2[ i, i-1 ]:= o; od;
      for i in [ n/2+1 .. n-1 ] do mat2[ i, i+1 ]:= o; od;
      mat2[ 1, 1 ]:= o;
      mat2[1,n/2+1]:= e;
      mat2[n-1,n/2]:= e^-1;
      mat2[n, n/2 ]:= -e^-1;

    elif n = 3 and q = 2 then

      mat1:= [ [o,z,z], [0,o,z^2], [0,0,o] ] * o;
      mat2:= [ [z,o,o], [o,o, 0 ], [o,0,0] ] * o;

    else

      mat1[(n-1)/2  ,(n-1)/2  ]:= z;
      mat1[(n-1)/2+1,(n-1)/2+1]:= z^q/z;
      mat1[(n-1)/2+2,(n-1)/2+2]:= z^-q;

      for i in [ 1 .. (n-1)/2-1 ] do mat2[ i, i+1 ]:= o; od;
      for i in [ (n-1)/2+3 .. n ] do mat2[ i, i-1 ]:= o; od;
      mat2[(n-1)/2,    1    ]:=  -(1+z^q/z)^-1;
      mat2[(n-1)/2,(n-1)/2+1]:= -o;
      mat2[(n-1)/2,    n    ]:=  o;
      mat2[(n-1)/2+1,  1    ]:= -o;
      mat2[(n-1)/2+1,(n-1)/2+1]:= -o;
      mat2[(n-1)/2+2,  1  ]:=  o;
    fi;

    return [ mat1, mat2 ];
end );

# Construction as in Proposition 6.6 of [HR05]
BindGlobal("GammaLMeetSU",
function(d, q, s)
    local F, As, Bs, Cs, Fs, m, gammaL1, Y, AandB, C, D, i,
    range, AsInGU, omega, generators, size, result, standardForm, formMatrix,
    j, u, v, B;
    if d mod s <> 0 or not IsPrime(s) or not IsOddInt(s) then
        ErrorNoReturn("<s> must be an odd prime and a divisor of <d>");
    fi;
    F := GF(q ^ 2);
    gammaL1 := MatricesInducingGaloisGroupOfGFQToSOverGFQ(s, q ^ 2);
    # Let w be a primitive element of GF(q ^ (2 * s)) over GF(q ^ 2). Since As is the
    # companion matrix of the minimal polynomial of w over GF(q ^ 2), its
    # determinant is (-1) ^ s times the constant term of said minimal
    # polynomial. By Vieta, this constant term is (-1) ^ s * the product of
    # all Galois conjugates of w. Hence, det(As) = w ^ ((q ^ (2 * s) - 1) / (q ^ 2 - 1)).
    As := gammaL1.A;
    # By Lemma 6.2 det(Bs) = (-1) ^ (s - 1). Bs has order s as it is the
    # Frobenius of the extension GF(q ^ 2) <= GF(q ^ (2 * s)).
    Bs := gammaL1.B;
    # Raise As to the (q ^ s - 1)-th power so that the result is in GammaU(1, q ^ s).
    # AsInGU now has order q ^ s + 1 (as As had order q ^ (2 * s) - 1).
    # det(AsInGU) = w ^ ((q ^ (2 * s) - 1) / (q + 1) * (q ^ s - 1) / (q - 1))
    AsInGU := As ^ (q ^ s - 1);
    # s is odd so (q ^ s - 1) / (q - 1) = 1 + q + ... + q ^ (s - 1) and q + 1
    # are coprime. Hence, we have to raise AsInGU to the (q + 1)-th power to
    # make the determinant 1. Cs has order (q ^ s + 1) / (q + 1).
    Cs := AsInGU ^ (q + 1);
    m := QuoInt(d, s);
    
    # Size according to Table 2.6 of [BHR13]
    size := SizeSU(d / s, q ^ s) * (q ^ s + 1) / (q + 1) * s;

    if m = 1 then
        # note that we require s to be odd
        generators := [Bs, Cs];
    
    else
        omega := Indeterminate(GF(q ^ (2 * s)));

        # The following two matrices generate SU(m, q ^ s) as a subgroup of SU(d, q)
        AandB := SpecialUnitaryGroupGens(m, q ^ s, omega);
        AandB := List(AandB, g -> MapGammaLToGLRatFun(g, As));

        # Note that GUMinusSU(m, q ^ s) ^ (q + 1) has determinant 1.
        C := IdentityMat(m, DefaultField(omega));
        C[1, 1] := omega ^ (q + 1);
        C[m, m] := (omega ^ (-q ^ s)) ^ (q + 1);
        C := MapGammaLToGLRatFun(C, As);

        # det(D) = 1
        D := IdentityMat(d, GF(q));
        for i in [0..m - 1] do
            range := [i * s + 1..(i + 1) * s];
            D{range}{range} := Bs;
        od;

        generators := Concatenation(AandB, [C, D]);
    fi;

    # Calculate the form preserved by the constructed group
    standardForm := InvariantSesquilinearForm(SU(m, q ^ s)).matrix;
    formMatrix := TakeTraceOfSesquilinearForm(standardForm, q ^ 2, s, "U-U");
    result := MatrixGroupWithSize(F, generators, size);
    SetInvariantSesquilinearForm(result, rec(matrix := formMatrix));

    # Conjugate the result so that it preserves the standard unitary form 
    return ConjugateToStandardForm(result, "U");
end);

# Construction as in Proposition 6.4 of [HR05]
BindGlobal("SymplecticSemilinearSp",
function(d, q, s)
    local F, gammaL1, As, Bs, m, omega, AandB, C, i, range, generators, size,
    standardForm, formMatrix, B, j, u, v, result;
    if d mod s <> 0 or not IsPrime(s) then
        ErrorNoReturn("<s> must be prime and a divisor of <d>");
    fi;
    if not IsEvenInt(QuoInt(d, s)) then
        ErrorNoReturn("The quotient <d> / <s> must be even");
    fi;
    F := GF(q);
    gammaL1 := MatricesInducingGaloisGroupOfGFQToSOverGFQ(s, q);
    # Let w be a primitive element of GF(q ^ s) over GF(q). Since As is the
    # companion matrix of the minimal polynomial of w over GF(q), its
    # determinant is (-1) ^ s times the constant term of said minimal
    # polynomial. By Vieta, this constant term is (-1) ^ s * the product of
    # all Galois conjugates of w. Hence, det(As) = w ^ ((q ^ s - 1) / (q - 1)).
    As := gammaL1.A;
    # By Lemma 6.2 det(Bs) = (-1) ^ (s - 1).
    Bs := gammaL1.B;
    m := QuoInt(d, s);

    omega := PrimitiveRoot(GF(q ^ s));
    AandB := List(GeneratorsOfGroup(Sp(m, q ^ s)), g -> MapGammaLToGL(g, As, omega));

    C := IdentityMat(d, F);
    for i in [0..m - 1] do
        range := [i * s + 1..(i + 1) * s];
        C{range}{range} := Bs;
    od;

    generators := Concatenation(AandB, [C]);
    # Size according to Table 2.6 of [BHR13]
    size := SizeSp(m, q ^ s) * s;

    # Calculate the form preserved by the constructed group
    standardForm := AntidiagonalHalfOneMat(d / s, F);
    formMatrix := TakeTraceOfSesquilinearForm(standardForm, q, s, "S-S");
    result := MatrixGroupWithSize(F, generators, size);
    SetInvariantBilinearForm(result, rec(matrix := formMatrix));

    # Conjugate the result so that it preserves the standard symplectic form 
    return ConjugateToStandardForm(result, "S");
end);

# Construction as in Proposition 6.5 of [HR05]
BindGlobal("UnitarySemilinearSp",
function(d, q)
    local F, gammaL1, A2, B2, omega, AandB, i, m, C, j, 
    range, generators, size, standardForm, formMatrix, result;
    if d mod 2 <> 0 then
        ErrorNoReturn("<d> must be divisible by 2");
    fi;
    if q mod 2 = 0 then
        ErrorNoReturn("<q> must be odd");
    fi;

    F := GF(q);
    gammaL1 := MatricesInducingGaloisGroupOfGFQToSOverGFQ(2, q);
    # Let w be a primitive element of GF(q ^ 2) over GF(q). Since A2 is the
    # companion matrix of the minimal polynomial of w over GF(q), its
    # determinant is (-1) ^ 2 times the constant term of said minimal
    # polynomial. By Vieta, this constant term is (-1) ^ 2 * the product of
    # all Galois conjugates of w. Hence, det(A2) = w ^ ((q ^ s - 1) / (q - 1))
    #                                            = w ^ (q + 1).
    A2 := gammaL1.A;
    # By Lemma 6.2 det(B2) = (-1) ^ (s - 1) = -1.
    B2 := gammaL1.B;

    omega := PrimitiveElement(GF(q ^ 2));
    AandB := GeneralUnitaryGroupGens(d / 2, q, Indeterminate(GF(q ^ 2)));
    AandB := List(AandB, g -> MapGammaLToGLRatFun(g, A2));

    # Choose i such that (q + 1) / 2 ^ i is odd
    i := PValuation(q + 1, 2);
    # Note that det(A2 ^ m) = -1, i.e. det(B2 * A2 ^ m) = 1
    m := (q ^ 2 - 1) / (2 ^ (i + 1));
    C := IdentityMat(d, F);
    for j in [0..d / 2 - 1] do
        C{[2 * j + 1, 2 * j + 2]}{[2 * j + 1, 2 * j + 2]} := B2 * A2 ^ m;
    od;

    generators := Concatenation(AandB, [C]);
    # Size according to Table 2.6 of [BHR13]
    size := SizeGU(d / 2, q) * 2; 

    # Calculate the form preserved by the constructed group
    standardForm := omega ^ ((q + 1) / 2) * InvariantSesquilinearForm(GU(d / 2, q)).matrix;
    formMatrix := TakeTraceOfSesquilinearForm(standardForm, q, 2, "U-S");
    result := MatrixGroupWithSize(F, generators, size);
    SetInvariantBilinearForm(result, rec(matrix := formMatrix));

    # Conjugate the result so that it preserves the standard symplectic form 
    return ConjugateToStandardForm(result, "S");
end);

# For a quadratic form Q on the vector space GF(q ^ s) ^ (d / s) given 
# by the Gram matrix <form>, we can interpret any v in GF(q) ^ d as an element of 
# GF(q ^ s) ^ (d / s) via the standard basis. Taking the trace of Q(v)
# yields a quadratic form Q' on the vector space GF(q) ^ d. Furthermore, if
# beta is the polar form of Q, then the polar form beta' of Q' is given by
# beta'(u, v) = Tr(beta(u, v)), where u, v are again to be interpreted as
# elements of GF(q ^ s) ^ (d / s) on the right-hand side.
#
# Note that we assume that <form> is an upper-triangular matrix.
BindGlobal("TakeTraceOfQuadraticForm",
function(form, q, s)
    local F, d, newForm, B, i, j, eiOverGFqsEntry, eiOverGFqsIndex,
    ejOverGFqsEntry, ejOverGFqsIndex, valueOfPolarForm, valueOfQuadraticForm;

    F := GF(q);
    d := s * Size(form);
    newForm := NullMat(d, d, F);
    B := CanonicalBasis(AsField(F, GF(q ^ s)));

    for i in [1..d] do
        # The basis vector ei of GF(q) ^ d corresponds to a vector in 
        # GF(q ^ s) ^ (d / s) with the entry eiOverGFqsEntry in the 
        # eiOverGFqsIndex-th component.
        eiOverGFqsEntry := B[(i - 1) mod s + 1];
        eiOverGFqsIndex := QuoInt(i - 1, s) + 1;

        for j in [i + 1..d] do
            ejOverGFqsEntry := B[(j - 1) mod s + 1];
            ejOverGFqsIndex := QuoInt(j - 1, s) + 1;
            
            if eiOverGFqsIndex <> ejOverGFqsIndex then
                valueOfPolarForm := eiOverGFqsEntry * form[eiOverGFqsIndex, ejOverGFqsIndex] 
                                                    * ejOverGFqsEntry;
            else
                valueOfPolarForm := 2 * eiOverGFqsEntry * form[eiOverGFqsIndex, ejOverGFqsIndex]
                                                        * ejOverGFqsEntry;
            fi;
            newForm[i, j] := TraceOverFiniteField(valueOfPolarForm, q, s);
        od;

        valueOfQuadraticForm := eiOverGFqsEntry ^ 2 * form[eiOverGFqsIndex, eiOverGFqsIndex];
        newForm[i, i] := TraceOverFiniteField(valueOfQuadraticForm, q, s);
    od; 

    return newForm;
end);

# Construction as in Lemma 6.3 of [HR10]
BindGlobal("GammaLMeetOmega",
function(epsilon, d, q, s)
    local F, gammaL1, gammaA, gammaB, Q, conjugatedOmega, zeta, AandB, size, C,
    result, formMatrix;
    
    if d mod s <> 0 or not IsPrime(s) then
        ErrorNoReturn("<s> must be a prime divisor of <d>");
    elif s = 2 then
        ErrorNoReturn("<s> must be odd");
    fi;

    if d / s < 3 then 
        ErrorNoReturn("<d> / <s> must be at least 3");
    fi;

    if not epsilon in [-1, 0, 1] then
        ErrorNoReturn("<epsilon> must be one of -1, 0, 1");
    elif epsilon = 0 and IsEvenInt(d) then
        ErrorNoReturn("<epsilon> cannot be zero if <d> is even");
    elif epsilon <> 0 and IsOddInt(d) then
        ErrorNoReturn("<epsilon> must be zero if <d> is odd");
    fi;

    F := GF(q);
    gammaL1 := MatricesInducingGaloisGroupOfGFQToSOverGFQ(s, q);
    gammaA := gammaL1.A;
    # By Lemma 6.2 of [HR05], det(gammaB) = (-1) ^ (s - 1) = 1.
    gammaB := gammaL1.B;

    Q := StandardOrthogonalForm(epsilon, d / s, q).Q;
    conjugatedOmega := ConjugateToSesquilinearForm(Omega(epsilon, d / s, q ^ s), "O-Q", Q);
    zeta := PrimitiveElement(GF(q ^ s));
    # These matrices generate a group isomorphic to Omega(epsilon, d / s, q ^ s) 
    # as a subgroup of Omega(epsilon, d, q)
    AandB := List(GeneratorsOfGroup(conjugatedOmega), g -> MapGammaLToGL(g, gammaA, zeta));

    # C has order s
    C := MatrixByBlockMatrix(BlockMatrix(List([1..d / s], i -> [i, i, gammaB]), d / s, d / s));

    # Size according to Table 2.6 of [BHR13]
    size := SizeOmega(epsilon, d / s, q ^ s) * s;
    result := MatrixGroupWithSize(F, Concatenation(AandB, [C]), size);

    # The constructed group preserves the quadratic form given by <formMatrix>
    formMatrix := TakeTraceOfQuadraticForm(Q, q, s);
    SetInvariantQuadraticFormFromMatrix(result, formMatrix);
    
    if epsilon = 0 then
        return ConjugateToStandardForm(result, "O");
    elif epsilon = 1 then
        return ConjugateToStandardForm(result, "O+");
    elif epsilon = -1 then
        return ConjugateToStandardForm(result, "O-");
    fi;
end);

# Let k be a unitary form over GF(q ^ 2) ^ (d / 2). We can consider a vector v
# in GF(q) ^ d as an element of GF(q ^ 2) ^ (d / 2) via the standard basis of
# GF(q ^ 2) over GF(q). Then Q(v) = k(v, v) defines a quadratic form Q on
# GF(q) ^ d. 
#
# Return the Gram matrix of the quadratic form Q given the Gram matrix
# <form> of the unitary form k.
BindGlobal("UnitaryFormToQuadraticForm",
function(form, q)
    local F, d, newForm, B, i, eiOverGFqsEntry, eiOverGFqsIndex, j,
    ejOverGFqsEntry, ejOverGFqsIndex, valueOfPolarForm, valueOfQuadraticForm;

    F := GF(q);
    d := NrRows(form) * 2;
    
    newForm := NullMat(d, d, F);
    B := CanonicalBasis(AsField(F, GF(q ^ 2)));

    for i in [1..d] do
        # The basis vector ei of GF(q) ^ d corresponds to a vector in 
        # GF(q ^ s) ^ (d / s) with the entry eiOverGFqsEntry in the 
        # eiOverGFqsIndex-th component.
        eiOverGFqsEntry := B[(i - 1) mod 2 + 1];
        eiOverGFqsIndex := QuoInt(i - 1, 2) + 1;

        for j in [i + 1..d] do
            ejOverGFqsEntry := B[(j - 1) mod 2 + 1];
            ejOverGFqsIndex := QuoInt(j - 1, 2) + 1;

            valueOfPolarForm := eiOverGFqsEntry * form[eiOverGFqsIndex, ejOverGFqsIndex]
                                                * ejOverGFqsEntry ^ q;

            newForm[i, j] := TraceOverFiniteField(valueOfPolarForm, q, 2);
        od;

        valueOfQuadraticForm := eiOverGFqsEntry ^ (q + 1) * form[eiOverGFqsIndex, eiOverGFqsIndex];
        newForm[i, i] := valueOfQuadraticForm;
    od; 

    return newForm;
end);

# Construction as in Lemma 6.5 of [HR10]
BindGlobal("UnitarySemilinearOmega",
function(d, q)
    local F, epsilon, generators, gammaL1, gammaA, gammaB, xi, AandB, B1,
    unitaryForm, formMatrix, bilinearForm, C, D, size, result;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even");
    fi;

    F := GF(q);
    epsilon := (-1) ^ (d / 2);

    gammaL1 := MatricesInducingGaloisGroupOfGFQToSOverGFQ(2, q);
    gammaA := gammaL1.A;
    gammaB := gammaL1.B;

    xi := Indeterminate(GF(q ^ 2));

    if IsOddInt(q) then
        # construct 1 / 2 * GU(d / 2, q)
        AandB := SpecialUnitaryGroupGens(d / 2, q, xi);
        AandB := List(AandB, g -> MapGammaLToGLRatFun(g, gammaA));
        # the determinant of B1 is always a (q + 1) / 2 - th root of unity,
        # i.e. B1 has order (q + 1) / 2 wrt SU(d / 2, q), which is what we want
        # since [GU : SU] = q + 1
        B1 := GeneralUnitaryGroupGens(d / 2, q, xi)[1] ^ 2;
        B1 := MapGammaLToGLRatFun(B1, gammaA);
        generators := Concatenation(AandB, [B1]);
    else
        # construct GU(d / 2, q)
        AandB := GeneralUnitaryGroupGens(d / 2, q, xi);
        AandB := List(AandB, g -> MapGammaLToGLRatFun(g, gammaA));
        generators := AandB;
    fi; 

    # the constructed group preserves the quadratic form given by <formMatrix>
    unitaryForm := InvariantSesquilinearForm(GU(d / 2, q)).matrix;
    formMatrix := UnitaryFormToQuadraticForm(unitaryForm, q);
    bilinearForm := formMatrix + TransposedMat(formMatrix);

    if epsilon = 1 then
        # construct an element of order 2 induced by the Frobenius of GF(q ^ 2)
        # over GF(q)
        C := MatrixByBlockMatrix(BlockMatrix(List([1..d / 2], i -> [i, i, gammaB]), d / 2, d / 2));
        if FancySpinorNorm(bilinearForm, F, C) = 1 then
            Add(generators, C);
        else
            # SpinorNorm(D) = -1
            # TODO Why is this true???
            D := GeneralUnitaryGroupGens(d / 2, q, xi)[1];
            D := MapGammaLToGLRatFun(D, gammaA);
            Assert(0, FancySpinorNorm(bilinearForm, F, C * D) = 1);
            Add(generators, C * D);
        fi;
    fi;

    # Size according to Lemma 6.5 in [HR10]
    size := 1 / 2 * SizeGU(d / 2, q);
    if epsilon = 1 then
        size := 2 * size;
    fi;
    if IsEvenInt(q) then
        size := 2 * size;
    fi;
    result := MatrixGroupWithSize(F, generators, size);

    SetInvariantQuadraticFormFromMatrix(result, formMatrix);
    
    if epsilon = 1 then
        return ConjugateToStandardForm(result, "O+");
    else
        return ConjugateToStandardForm(result, "O-");
    fi;
end);

# Construction as in Lemma 6.4 of [HR10]
BindGlobal("OrthogonalSemilinearOmega",
function(epsilon, epsilon1, d, q)
    local F, gammaL1, gammaA, gammaB, Q, dummyGroup, conjugation, 
    oldToIntermediate, intermediateToNew, formMatrix, bilinearForm, 
    orthogonalGenerators, zeta, AandB, C, S, TauS, G, TauG, generators, 
    CS, size, result;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even");
    fi;
    if not epsilon in [-1, 1] then
        ErrorNoReturn("<epsilon> must be -1 or 1");
    fi;
    if epsilon1 <> 0 then
        if IsOddInt(d / 2) then
            ErrorNoReturn("<epsilon1> must be 0 if <d> / 2 is odd");
        fi;
        if d / 2 < 3 then
            ErrorNoReturn("<d> / 2 must be at least 3 if <epsilon> = <epsilon1>");
        fi;
    elif epsilon1 = 0 then
        if IsEvenInt(q * d / 2) then
            ErrorNoReturn("<q> * <d> / 2 must be odd if <epsilon> <> <epsilon1>");
        fi;
    fi;

    F := GF(q);
    zeta := PrimitiveElement(GF(q ^ 2));
    gammaL1 := MatricesInducingGaloisGroupOfGFQToSOverGFQ(2, q);
    gammaA := gammaL1.A;
    # By Lemma 6.2 of [HR05], det(gammaB) = -1.
    gammaB := gammaL1.B;

    Q := StandardOrthogonalForm(epsilon1, d / 2, q ^ 2).Q;
    formMatrix := TakeTraceOfQuadraticForm(Q, q, 2);
    bilinearForm := formMatrix + TransposedMat(formMatrix);

    orthogonalGenerators := StandardGeneratorsOfOrthogonalGroup(epsilon1, d / 2, q ^ 2);
    AandB := orthogonalGenerators.generatorsOfOmega;
    S := orthogonalGenerators.S;
    G := orthogonalGenerators.G;
    AandB := List(AandB, g -> MapGammaLToGL(g, gammaA, zeta));
    TauS := MapGammaLToGL(S, gammaA, zeta);
    TauG := MapGammaLToGL(G, gammaA, zeta);

    generators := AandB;

    # C has order 2
    C := MatrixByBlockMatrix(BlockMatrix(List([1..d / 2], i -> [i, i, gammaB]), d / 2, d / 2));

    if epsilon = 1 and d mod 4 = 0 then
        if IsEvenInt(q) then
            # det(C) = (-1) ^ (d / 2) = 1
            Add(generators, C);
            Add(generators, MapGammaLToGL(S, gammaA, zeta));
        else
            if FancySpinorNorm(bilinearForm, F, TauG) = 1 then
                Add(generators, TauG);
            else
                # SpinorNorm(TauS) = -1
                Add(generators, TauS * TauG);
            fi;
            if FancySpinorNorm(bilinearForm, F, C) = 1 then
                # det(C) = (-1) ^ (d / 2) = 1
                Add(generators, C);
            else
                # SpinorNorm(TauS) = -1
                Add(generators, TauS * C);
            fi;
        fi;

        # Size according to Lemma 6.4 of [HR10]
        size := SizeOmega(1, d / 2, q ^ 2) * 4;
    elif epsilon = -1 and d mod 4 = 0 then
        if IsEvenInt(q) then
            Add(generators, TauS);
        else
            if FancySpinorNorm(bilinearForm, F, TauG) = 1 then
                Add(generators, TauG);
            else
                # SpinorNorm(TauS) = -1
                Add(generators, TauS * TauG);
            fi;
        fi;

        # Size according to Lemma 6.4 of [HR10]
        size := SizeOmega(-1, d / 2, q ^ 2) * 2;
    else
        # d mod 4 = 2 and q odd
        if epsilon * (-1) ^ (d * (q - 1) / 4) = -1 then
            # formMatrix represents a quadratic form of non-square discriminant
            # by Lemma 3.3 of [HR10]
            if FancySpinorNorm(bilinearForm, F, TauS) = 1 then
                Add(generators, TauS);
            else
                # -I is not in Omega(epsilon, d, q) if the quadratic form has
                # non-square discriminant
                Add(generators, -TauS);
            fi;

            # Size according to Lemma 6.4 of [HR10]
            size := SizeOmega(0, d / 2, q ^ 2) * 2;
        else
            # formMatrix represents a quadratic form of square discriminant
            CS := C * MatrixByBlockMatrix(BlockMatrix(List([1..d / 2], 
                                                           i -> [i, i, gammaA ^ ((q - 1) / 2)]), 
                                                      d / 2, d / 2));

            # In this case, contrary to what [HR10] suggests, the quadratic
            # form preserved by the constructed group is *not* obtained by
            # taking the trace of some quadratic form on GF(q ^ 2) ^ (d / 2).
            bilinearForm := BilinearForm(Group(Concatenation(generators, [CS])), "O");
            formMatrix := BilinearToQuadraticForm(bilinearForm);

            if FancySpinorNorm(bilinearForm, F, CS) = 1 then
                Add(generators, CS);
            else
                # SpinorNorm(TauS) = -1
                Add(generators, TauS * CS);
            fi;

            # Size according to Lemma 6.4 of [HR10]
            size := 2 * SizeOmega(0, d / 2, q ^ 2) * 2;
        fi;
    fi;

    result := MatrixGroupWithSize(F, generators, size);

    # The constructed group preserves the quadratic form given by <formMatrix>
    SetInvariantQuadraticFormFromMatrix(result, formMatrix);

    if epsilon = 1 then
        return ConjugateToStandardForm(result, "O+");
    else
        return ConjugateToStandardForm(result, "O-");
    fi;
end);
