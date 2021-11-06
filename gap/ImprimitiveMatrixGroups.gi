# Return the subgroup of <M>SL(n, q)</M> stabilising a
# decomposition <M>F^n=V_1\oplus V_2\oplus\dots\oplus V_t</M> of <M>F^n</M>,
# where <C>F := GF(q)</C>, as a direct sum of vector spaces of equal
# dimensions. Note that this means that <A>t</A> must be a divisor of <A>n</A>.
# We demand that <A>t</A> be greater than 1.
# Construction as in Proposition 5.1 of [HR05]
BindGlobal("ImprimitivesMeetSL", 
function(n, q, t)
    local det, E, gens, i, newGen, newGens, wreathProduct, z, F, m, size;
    if t = 1 or (n mod t) <> 0 then
        ErrorNoReturn("<t> must be greater than 1 and a divisor of <n> but <t> = ", t,
                      " and <n> = ", n);
    fi;
    m := QuoInt(n, t);
    wreathProduct := MatWreathProduct(SL(m, q), SymmetricGroup(t));
    gens := GeneratorsOfGroup(wreathProduct);
    # newGens will be analogous to A, B, C, D in [HR05]
    newGens := [];
    for i in [1..Length(gens)] do
        det := Determinant(gens[i]);
        if IsOne(det) then
            Add(newGens, gens[i]);
        else
            # rescale first column by -1
            newGen := gens[i] * DiagonalMat(Z(q) ^ 0
                * Concatenation([-1], List([2..n], i -> 1)));
            Add(newGens, newGen);
        fi;
    od;
    F := GF(q);
    z := PrimitiveElement(F);
    E := DiagonalMat(
        Concatenation([z], List([2..m], i -> z ^ 0),
                      [z ^ -1], List([m + 2..n], i -> z ^ 0))
    );
    Add(newGens, E);
    # Size according to Table 2.5 of [BHR13]
    size := SizeSL(n / t, q) ^ t * (q - 1) ^ (t - 1) * Factorial(t);
    return MatrixGroupWithSize(F, newGens, size);
end);

# Construction as in Proposition 5.4 of [HR05]
# We stabilise the decomposition with the summands 
# < e_1, e_2, ..., e_m >, < e_{m + 1}, ..., e_{2m} >, ..., 
# < e_{d - m + 1}, ..., e_d > using the form I_d.
BindGlobal("SUNonDegenerateImprimitives",
function(d, q, t)
    local m, F, zeta, SUChangedForm, generators, generatorOfSU, generator, C, 
    D1, D, E, result, size;
    if t = 1 or (d mod t) <> 0 then
        ErrorNoReturn("<t> must be greater than 1 and a divisor of <d> but <t> = ", t,
                      " and <d> = ", d);
    fi;
    m := QuoInt(d, t);
    generators := [];
    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);

    # generate SU(m, q)
    #
    # We have to exclude m = 1 since the Forms package has a bug in this case;
    # however, this case is trivial.
    if m > 1 then
        SUChangedForm := ConjugateToSesquilinearForm(SU(m, q), "U", IdentityMat(m, F));
    else
        SUChangedForm := SU(m, q);
    fi;
    for generatorOfSU in GeneratorsOfGroup(SUChangedForm) do
        generator := IdentityMat(d, F);
        generator{[1..m]}{[1..m]} := generatorOfSU;
        Add(generators, generator);
    od;

    # A matrix interchanging v_i with -v_{i + m} for 1 <= i <= m 
    # (i.e. a 2-cycle in Sym(t)).
    C := IdentityMat(d, F);
    C{[1..m]}{[1..m]} := NullMat(m, m, F);
    C{[m + 1..2 * m]}{[m + 1..2 * m]} := NullMat(m, m, F);
    C{[1..m]}{[m + 1..2 * m]} := - IdentityMat(m, F);
    C{[m + 1..2 * m]}{[1..m]} := - IdentityMat(m, F);
    # det(C) = (-1) ^ m (if we interchange the columns i and i + m for 
    # 1 <= i <= m, C turns into a diagonal matrix of determinant 1) so we fix
    # the determinant if m is odd. Note that [HR05] forgets to do this.
    if IsOddInt(m) then
        C := DiagonalMat(Concatenation([-zeta ^ 0], List([2..d], i -> zeta ^ 0))) * C;
    fi;
    Add(generators, C);

    # A matrix shifting v_i to v_{i + m} where indices are to be understood mod d
    # (i.e. a t-cycle in Sym(t)).
    D1 := BlockMatrix(List([1..t], i -> [i, i mod t + 1, IdentityMat(m, F)]), t, t);
    # det(D) = 1 since det(D1) = (-1) ^ (m * (d - m))
    if IsEvenInt(m) or IsEvenInt(q) or IsOddInt(t) then 
        D := D1;
    else
        D := DiagonalMat(Concatenation([- zeta ^ 0], List([2..d], i -> zeta ^ 0))) * D1;
    fi;
    Add(generators, D);

    # Finally a matrix allowing to "shift determinants around between blocks"
    E := DiagonalMat(Concatenation([zeta ^ (q - 1)],
                                   List([2..m], i -> zeta ^ 0),
                                   [zeta ^ (1 - q)],
                                   List([m + 2..d], i -> zeta ^ 0)));
    Add(generators, E);

    # Size according to Table 2.5 of [BHR13]
    size := SizeSU(m, q) ^ t * (q + 1) ^ (t - 1) * Factorial(t);
    result := MatrixGroupWithSize(F, generators, size);
    # change back fixed form into standard GAP form Antidiag(1, ..., 1)
    SetInvariantSesquilinearForm(result, rec(matrix := IdentityMat(d, F)));

    return ConjugateToStandardForm(result, "U");
end);

# Construction as in Proposition 5.5 of [HR05]
# The decomposition stabilized is given by the summands 
# < e_1, ..., e_{d / 2} > and < f_{d / 2}, ..., f_1 >, 
# where (e_1, ..., e_{d / 2}, f_{d / 2}, ..., f_1) is the standard basis.
BindGlobal("SUIsotropicImprimitives",
function(d, q)
    local F, zeta, generators, J, generatorOfSL,
    generator, C, D, size;
    if not IsEvenInt(d) then
        ErrorNoReturn("<d> must be even but <d> = ", d);
    fi;

    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);
    generators := [];
    J := AntidiagonalMat(d / 2, F);

    # first generate SL(d / 2, q ^ 2) as a subgroup of SU(d, q)
    for generatorOfSL in GeneratorsOfGroup(SL(d / 2, q ^ 2)) do
        generator := NullMat(d, d, F);
        generator{[1..d / 2]}{[1..d / 2]} := generatorOfSL;
        generator{[d / 2 + 1..d]}{[d / 2 + 1..d]} := J * HermitianConjugate(generatorOfSL, q) ^ (-1) 
                                                       * J;
        Add(generators, generator);
    od;

    # now a matrix switching the two summands
    C := NullMat(d, d, F);
    C{[1..d / 2]}{[d / 2 + 1..d]} := IdentityMat(d / 2, F);
    C{[d / 2 + 1..d]}{[1..d / 2]} := IdentityMat(d / 2, F);
    # We have det(C) = 1 if d = 0 mod 4 and det(C) = -1 if d = 2 mod 4.
    # Hence, if d = 2 mod 4 and q is odd, we have to multiply C with a matrix
    # of determinant -1.
    if d mod 4 <> 0 and IsOddInt(q) then
        C := C * DiagonalMat(Concatenation([zeta ^ QuoInt(q + 1, 2)],
                                           List([2..d - 1], i -> zeta ^ 0),
                                           [zeta ^ (-q * QuoInt(q + 1, 2))]));
    fi;
    Add(generators, C);

    # Finally a diagonal matrix accounting for the fact that the determinants
    # of the two blocks can be anything as long as they multiply to 1
    # Note that the original Magma code and [HR05] use
    #   D := DiagonalMat(Concatenation([zeta, zeta ^ q], 
    #                                  List([3..d - 2], i -> zeta ^ 0),
    #                                  [zeta ^ (-1), zeta ^ (-q)]));
    # but this obviously does not work for d = 2; the construction below,
    # however, works for all d.
    D := DiagonalMat(Concatenation([zeta ^ (q + 1)],
                                   List([2..d - 1], i -> zeta ^ 0),
                                   [zeta ^ (-q - 1)]));
    Add(generators, D);

    # Size according to Table 2.5 of [BHR13]
    size := SizeSL(d / 2, q ^ 2) * (q - 1) * 2;

    return MatrixGroupWithSize(F, generators, size);
end);


# Construction as in Proposition 5.2 of [HR05]
# We stabilise the decomposition with the t summands 
# < e_1, ..., e_k, f_k, ..., f_1 >,
# < e_{k + 1}, ..., e_{2k}, f_{2k}, ..., f_{k + 1} >, ...
# < e_{l - k + 1}, ..., e_{d / 2}, f_{d / 2}, ..., f_{l - k + 1} >,
# where l = d / 2, m = d / t and k = m / 2.
BindGlobal("SpNonDegenerateImprimitives",
function(d, q, t)
    local m, l, k, field, one, gens, Spgen, Xi, C, D;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even.");
    fi;

    m := QuoInt(d, t);

    if not m * t = d then
        ErrorNoReturn("<t> must divide <d>.");
    fi;

    if IsOddInt(m) then
        ErrorNoReturn("<m> = <d> / <t> must be even.");
    fi;

    l := QuoInt(d, 2);
    k := QuoInt(m, 2);

    field := GF(q);
    one := One(field);
    gens := [];

    # This construction is the same as in Proposition 4.4 of [HR05]
    # These generators are block matrices of the form
    # [[A 0 B], [0 C 0], [D 0 E]], which generate a subgroup
    # corresponding to Sp(m, q).
    for Spgen in GeneratorsOfGroup(Sp(m, q)) do
        Xi := IdentityMat(d, field);
        Xi{[1..k]}{[1..k]} := Spgen{[1..k]}{[1..k]};
        Xi{[1..k]}{[d - k + 1 .. d]} := Spgen{[1..k]}{[k + 1 .. 2 * k]};
        Xi{[d - k + 1 .. d]}{[1..k]} := Spgen{[k + 1 .. 2 * k]}{[1..k]};
        Xi{[d - k + 1 .. d]}{[d - k + 1 .. d]} := Spgen{[k + 1 .. 2 * k]}{[k + 1 .. 2 * k]};
        Add(gens, Xi);
    od;

    # This matrix will swap the vectors e_i with e_{i + k} and
    # f_i with f_{i + k} for 1 <= i <= k respectively,
    # which corresponds to the product of m transpositions in Sym(t).
    # Since m is even, this permutation has signum 1 and det(C) = 1.
    # One can easily check that this preserves the form.
    C := NullMat(d, d, field);

    # The central 2 * (l - m) = (d - 2m) basis vectors should be
    # unaffected, so an identity matrix as a block works nicely.
    C{[m + 1..d - m]}{[m + 1..d - m]} := IdentityMat(2 * (l - m), field);
    
    # This block matrix magic is just a
    # fancy way of swapping the correct entries.
    C{[1..k]}{[k + 1..m]} := IdentityMat(k, field);
    C{[k + 1..m]}{[1..k]} := IdentityMat(k, field);
    C{[d - k + 1..d]}{[d - m + 1..d - k]} := IdentityMat(k, field);
    C{[d - m + 1..d - k]}{[d - k + 1..d]} := IdentityMat(k, field);

    Add(gens, C);

    # In the case t = 2, we only need one element to generate Sym(t),
    # since 2-cycles (matrix C) and t-cycles (matrix D) are the same.
    # Analogously, the construction for D would just yield a copy of C,
    # so we do not need to do it again.
    if t <> 2 then

        # This Matrix will map the basis vectors
        # e_i -> e_{((i + k -1) mod l) + 1} and
        # f_i -> f_{((i + k -1) mod l) + 1} 
        # which corresponds to a t-cycle in Sym(t).
        # We have det(C) = 1 because we are effectively
        # swapping an even number of rows/colums.
        # One can easily check that this preserves the form.
        D := NullMat(d, d, field);

        # This block matrix magic is again just a
        # fancy way of swapping the correct entries.
        # Effectively, we are shifting t k x k - blocks
        # by k row/colums each.
        D{[1..l - k]}{[k + 1..l]} := IdentityMat(l - k, field);
        D{[l - k + 1..l]}{[1..k]} := IdentityMat(k, field);
        D{[l + 1..l + k]}{[d - k + 1..d]} := IdentityMat(k, field);
        D{[l + k + 1..d]}{[l + 1..d - k]} := IdentityMat(l - k, field);

        Add(gens, D);

    fi;

    return MatrixGroupWithSize(field, gens, SizeSp(m, q) ^ t * Factorial(t));

end);


# Construction as in Proposition 5.3 of [HR05]
# We stabilise the decomposition into the 2 subspaces
# < e_1, ..., e_l > and < f_l, ..., f_1 >.
BindGlobal("SpIsotropicImprimitives",
function(d, q)
    local l, field, one, gens, J, GLgen, AorB, C;

    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even.");
    fi;

    if IsEvenInt(q) then
        ErrorNoReturn("<q> must be odd.");
    fi;

    l := QuoInt(d, 2);

    field := GF(q);
    one := One(field);
    gens := [];
    J := AntidiagonalMat(l, field);
    
    # For either generator of Sp(d,q), we take an
    # invertible matrix AorB_1 which acts on
    # the first l basis vectors and put it in
    # a diagonal 2 x 2 block matrix with another
    # invertible matrix such that the form is preserved.
    # This way, the decomposition must also be preserved.
    for GLgen in GeneratorsOfGroup(GL(l, q)) do
        AorB := IdentityMat(d, field);
        AorB{[1..l]}{[1..l]} := GLgen;
        AorB{[l + 1 .. d]}{[l + 1 .. d]} := J * TransposedMat(GLgen ^ (-1)) * J;
        Add(gens, AorB);
    od;

    # This matrix effectively permutes the two subspaces.
    C := NullMat(d, d, field);
    C{[1..l]}{[l + 1..d]} := IdentityMat(l, field);
    C{[l + 1..d]}{[1..l]} := -IdentityMat(l, field);

    Add(gens, C);

    return MatrixGroupWithSize(field, gens, SizeGL(l, q) * 2);

end);
