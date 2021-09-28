# Return the subgroup of <M>SL(n, q)</M> stabilising a
# decomposition <M>F^n=V_1\oplus V_2\oplus\dots\oplus V_t</M> of <M>F^n</M>,
# where <C>F := GF(q)</C>, as a direct sum of vector spaces of equal
# dimensions. Note that this means that <A>t</A> must be a divisor of <A>n</A>.
# We demand that <A>t</A> be greater than 1.
# Construction as in Proposition 5.1 of [2]
BindGlobal("ImprimitivesMeetSL", 
function(n, q, t)
    local det, E, gens, i, newGen, newGens, wreathProduct, z, m, result;
    if t = 1 or (n mod t) <> 0 then
        ErrorNoReturn("<t> must be greater than 1 and a divisor of <n> but <t> = ", t,
                      " and <n> = ", n);
    fi;
    m := QuoInt(n, t);
    wreathProduct := MatWreathProduct(SL(m, q), SymmetricGroup(t));
    gens := GeneratorsOfGroup(wreathProduct);
    # newGens will be analogous to A, B, C, D in [2]
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
    z := PrimitiveElement(GF(q));
    E := DiagonalMat(
        Concatenation([z], List([2..m], i -> z ^ 0),
                      [z ^ -1], List([m + 2..n], i -> z ^ 0))
    );
    Add(newGens, E);
    result := Group(newGens);
    # Size according to Table 2.5 of [1]
    SetSize(result, Size(SL(n/t, q)) ^ t * (q-1) ^ (t-1) * Factorial(t));
    return result;
end);

# Construction as in Proposition 5.4 of [2]
# We stabilise the decomposition with the summands 
# < e_1, e_2, ..., e_m >, < e_{m + 1}, ..., e_{2m} >, ..., 
# < e_{d - m + 1}, ..., e_d > using the form I_d.
BindGlobal("SUNonDegenerateImprimitives",
function(d, q, t)
    local m, F, zeta, SUChangedForm, generators, generatorOfSU, generator, C, 
    D1, D, E, result;
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
        SUChangedForm := ChangeFixedSesquilinearForm(SU(m, q), "U", IdentityMat(m, F));
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
    # the determinant if m is odd. Note that [2] forgets to do this.
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

    result := Group(generators);
    # change back fixed form into standard GAP form Antidiag(1, ..., 1)
    SetInvariantSesquilinearForm(result, rec(matrix := IdentityMat(d, F)));
    result := ChangeFixedSesquilinearForm(result,
                                          "U",
                                          AntidiagonalMat(List([1..d], i -> 1), F));
    # Size according to Table 2.5 of [1]
    SetSize(result, Size(SU(m, q)) ^ t * (q + 1) ^ (t - 1) * Factorial(t));
    
    return result;
end);

# Construction as in Proposition 5.5 of [2]
# The decomposition stabilized is given by the summands 
# < e_1, ..., e_{d / 2} > and < f_{d / 2}, ..., f_1 >, 
# where (e_1, ..., e_{d / 2}, f_{d / 2}, ..., f_1) is the standard basis.
BindGlobal("SUIsotropicImprimitives",
function(d, q)
    local F, zeta, generators, J, generatorOfSL,
    generator, C, D, result;
    if not IsEvenInt(d) then
        ErrorNoReturn("<d> must be even but <d> = ", d);
    fi;

    F := GF(q ^ 2);
    zeta := PrimitiveElement(F);
    generators := [];
    J := AntidiagonalMat(List([1..d / 2], i -> 1), F);

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
    # Note that the original Magma code and [2] use
    #   D := DiagonalMat(Concatenation([zeta, zeta ^ q], 
    #                                  List([3..d - 2], i -> zeta ^ 0),
    #                                  [zeta ^ (-1), zeta ^ (-q)]));
    # but this obviously does not work for d = 2; the construction below,
    # however, works for all d.
    D := DiagonalMat(Concatenation([zeta ^ (q + 1)],
                                   List([2..d - 1], i -> zeta ^ 0),
                                   [zeta ^ (-q - 1)]));
    Add(generators, D);

    result := Group(generators);
    # Size according to Table 2.5 of [1]
    SetSize(result, Size(SL(d / 2, q ^ 2)) * (q - 1) * 2);

    return result;
end);
