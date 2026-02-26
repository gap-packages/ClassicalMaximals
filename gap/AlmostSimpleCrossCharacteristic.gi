InstallGlobalFunction("ModularReductionOfIntegralLattice",
function(L, q)
    local special, general, normaliser, G, AI, F, d, Q, M, C, CC, AC, modims, i,
          phi, M2, new, nc, na, perms, AG, OAG, gps, w, forms, ww, gens, sgens,
          a, iso, det, v, projectiveOrderIso, po, x, ox, f, ff, co, u, rts, got,
          form, rq, scal, quad, type, H, tmat, dsq, sgn, mat, c, j, o, k;

    special := ValueOption("special");
    if special = fail then special := false; fi;
    general := ValueOption("general");
    if general = fail then general := false; fi;
    normaliser := ValueOption("normaliser");
    if normaliser = fail then normaliser := false; fi;
    if normaliser then general := true; fi;
    if general then special := true; fi;

    G := L.G; AI := L.AI; F := L.F;
    d := DimensionOfMatrixGroup(G);
    Q := GroupByGenerators([G.1 * One(GF(q)), G.2 * One(GF(q))]);
    M := GModuleByMats(GeneratorsOfGroup(Q), GF(q));
    C := List(MTX.CollectedFactors(M), c -> c[1]);
    CC := [];
    for c in C do
        if not MTX.IsAbsolutelyIrreducible(c) then
            Error("Constituents are not absolutely irreducible over finite field.");
        fi;
        if c.dimension <> 1 then
            Add(CC, c);
        fi;
    od;
    C := CC;
    AC := List(C, c -> Group(c.generators));
    modims := [];
    i := 1;
    while i <= Size(C) do
        modims[i] := [];
        phi := GroupHomomorphismByImages(F, AC[i], [AC[i].1, AC[i].2]);
        for a in AI do
            M2 := GModuleByMats([phi(a[1]), phi(a[2])], GF(q));
            new := true;
            for j in [1..Size(C)] do
                if MTX.IsomorphismModules(C[j], M2) <> fail then
                    Add(modims[i], j);
                    new := false;
                    break;
                fi;
            od;
            if new then
                Add(C, M2);
                Add(AC, Group(M2.generators));
                Add(modims[i], Size(C));
            fi;
        od;
        i := i+1;
    od;
    nc := Size(C);
    na := Size(AI);
    if na = 0 then
        perms := [()];
    else
        perms := List([1..na], j -> PermList(List([1..nc], i -> modims[i,j])));
    fi;
    AG := Group(perms);
    OAG := Orbits(AG, [1..nc]);
    gps := [];
    w := PrimitiveElement(GF(q));
    for o in OAG do
        i := Representative(o);
        d := Degree(AC[i]);
        # test if the group fixes a form, and act accordingly.
        forms := CM_ClassicalForms(AC[i], GF(q));
        if forms.formType = "linear" then
            if general then
                ww := w;
            else
                ww := w^(QuoInt(q-1, Gcd(q-1,d)));
            fi;  # power of w s.t. ww I_d has det 1
            gens := ShallowCopy(GeneratorsOfGroup(AC[i]));
            # find generators of subgroup of automorphism group stabilizing this module
            sgens := [];
            for j in [1..na] do
                if i^perms[j] = i then
                    Add(sgens, j);
                fi;
            od;
            for j in sgens do
                # Attempt to append this automorphism to AC[i]
                a := AI[j];
                phi := GroupHomomorphismByImages(F, AC[i], [AC[i].1, AC[i].2]);
                M2 := GModuleByMats([phi(a[1]), phi(a[2])], GF(q));
                iso := MTX.IsomorphismModules(C[i], M2);
                Assert(0, iso <> fail);
                det := DeterminantMat(iso);
                v := RootFFE(GF(q), det, d);
                if v <> fail then
                    iso := iso * (v^-1 * IdentityMat(d, GF(q)));
                elif not general then
                    continue;
                fi;
                # We will try to make the order of iso as small as possible.
                # if general is true, we will sacrifice determinant 1 if necessary
                projectiveOrderIso := ProjectiveOrder(iso);
                po := projectiveOrderIso[1];  # iso^po = xI
                x := projectiveOrderIso[2];
                ox := Order(x);
                if ox > 1 then
                    f := PrimePowersInt(ox);
                    f := List([1..Length(f)/2], i -> [f[2*i-1], f[2*i]]);
                    ff := List(f, x -> ox / x[1]^x[2]);
                    co := GcdRepresentation(ff);
                    for i in [1..Size(f)] do
                        u := x^(co[i] * ff[i]);  # factor of x with order f[i,1]^f[i,2]
                        rts := RootsOfUPol(GF(q), X(GF(q))^po - u);
                        if rts <> [] then
                            got := false;
                            for v in rts do
                                if LogFFE(v, w) mod (QuoInt((q-1), Gcd(q-1, d))) = 0 then
                                    # v * I_d has det 1
                                    iso := iso * (v^-1 * IdentityMat(d, GF(q)));
                                    got := true;
                                    break;
                                fi;
                            od;
                            if general and not got then
                                iso := iso * (rts[1]^-1 * IdentityMat(d, GF(q)));
                            fi;
                        fi;
                    od;
                fi;
                Add(gens, iso);
            od;
            # Finally adoin scalars
            if (not general and  Gcd(q-1,d) <> 1) or (general and q > 2) then
                Add(gens, ww * IdentityMat(d, GF(q)));
            fi;
            Add(gps, GroupByGenerators(gens));
        elif forms.formType = "unitary" then
            form := forms.sesquilinearForm;
            f := PrimePowersInt(q);
            f := List([1..Length(f)/2], i -> [f[2*i-1], f[2*i]]);
            rq := f[1,1]^(QuoInt(f[1,2], 2));
            if normaliser then
                ww := w;
            elif general then
                ww := w^(rq - 1);
            else
                ww := w^((rq - 1) * (QuoInt((rq+1), Gcd(rq+1, d))));
            fi;  # power of w^(rq-1) s.t. ww I_d has det 1
            gens := ShallowCopy(GeneratorsOfGroup(AC[i]));
            # find generators of subgroup of automorphism group stabilizing this module
            sgens := [];
            for j in [1..na] do
                if i^perms[j] = i then
                    Add(sgens, j);
                fi;
            od;
            for j in sgens do
                # Attempt to append this automorphism to AC[i]
                a := AI[j];
                phi := GroupHomomorphismByImages(F, AC[i], [AC[i].1, AC[i].2]);
                M2 := GModuleByMats([phi(a[1]), phi(a[2])], GF(q));
                iso := MTX.IsomorphismModules(C[i], M2);
                Assert(0, iso <> fail);
                # adjust by scalar to make iso fix form.
                scal := (iso * form * TransposedMat(EntrywisePowerMat(iso, rq))* form^-1)[1,1];
                v := RootFFE(GF(q), scal * One(GF(q)), rq+1);
                Assert(0, v <> fail);
                iso := iso * (v^-1 * IdentityMat(d, GF(q)));
                # try to make determinant 1
                det := DeterminantMat(iso);
                rts := RootsOfUPol(GF(q), X(GF(q))^d - det);
                got := false;
                for v in rts do
                    if LogFFE(v, w) mod (rq - 1) = 0 then
                        iso := iso * (v^-1 * IdentityMat(d, GF(q)));
                        got := true;
                        break;
                    fi;
                od;
                if not general and not got then
                    continue;
                fi;
                # We will try to make the order of iso as small as possible.
                # if general is true, we will sacrifice determinant 1 if necessary
                # if normaliser is true, we will sacrifice fixing form if necessary
                projectiveOrderIso := ProjectiveOrder(iso);
                po := projectiveOrderIso[1];  # iso^po = xI
                x := projectiveOrderIso[2];
                ox := Order(x);
                if ox > 1 then
                    f := PrimePowersInt(ox);
                    f := List([1..Length(f)/2], i -> [f[2*i-1], f[2*i]]);
                    ff := List(f, x -> ox / x[1]^x[2]);
                    co := GcdRepresentation(ff);
                    for i in [1..Size(f)] do
                        u := x^(co[i] * ff[i]);  # factor of x with order f[i,1]^f[i,2]
                        rts := RootsOfUPol(GF(q), X(GF(q))^po - u);
                        if rts <> [] then
                            got := false;
                            for v in rts do
                                if LogFFE(v, w) mod ((rq-1)*(QuoInt((rq+1), Gcd(rq+1, d)))) = 0 then
                                    # v * I_d has det 1 and is in GU
                                    iso := iso * (v^-1 * IdentityMat(d, GF(q)));
                                    got := true;
                                    break;
                                fi;
                            od;
                            if general and not got then
                                for v in rts do
                                    if LogFFE(v, w) mod (rq-1) = 0 then
                                        # v * I_d fixes form
                                        iso := iso * (v^-1 * IdentityMat(d, GF(q)));
                                        got := true;
                                        break;
                                    fi;
                                od;
                                if normaliser and not got then
                                    iso := iso * (rts[1]^-1 * IdentityMat(d, GF(q)));
                                fi;
                            fi;
                        fi;
                    od;
                fi;
                Add(gens, iso);
            od;
            # finally adjoin scalars
            if general or Gcd(rq+1, d) <> 1 then
                Add(gens, ww * IdentityMat(d, GF(q)));
            fi;
            if normaliser then
                Add(gps, GroupByGenerators(gens));
            else
                Add(gps, ConjugateToStandardForm(GroupByGenerators(gens), "U", GF(q)));
            fi;
        else
            form := forms.bilinearForm;
            if IsEvenInt(q) and forms.quadraticForm <> false then
                quad := true;
                form := forms.quadraticForm;
            else
                quad := false;
            fi;
            if forms.formType = "orthogonalminus" then
                type := "O-";
            elif forms.formType = "orthogonalplus" then
                type := "O+";
            elif forms.formType = "orthogonalcircle" then
                type := "O";
            else
                type := "S";
            fi;
            H := ConjugateToStandardForm(AC[i], type, GF(q));
            gens := ShallowCopy(GeneratorsOfGroup(H));
            tmat := H!.baseChangeMatrix;
            # find generators of subgroup of automorphism group stabilizing this module
            sgens := [];
            for j in [1..na] do
                if i^perms[j] = i then
                    Add(sgens, j);
                fi;
            od;
            if forms.formType = "orthogonalplus" then
                dsq := d mod 4 = 0 or (d mod 4 = 2 and q mod 4 = 1);
                sgn := 1;
            elif forms.formType = "orthogonalminus" then
                dsq := d mod 4 = 2 and q mod 4 = 3;
                sgn := -1;
            else
                dsq := false;
                sgn := 0;
            fi;
            for j in sgens do 
                # Attempt to append this automorphism to AC[i]
                a := AI[j];
                phi := GroupHomomorphismByImages(F, AC[i], [AC[i].1, AC[i].2]);
                M2 := GModuleByMats([phi(a[1]), phi(a[2])], GF(q));
                iso := MTX.IsomorphismModules(C[i], M2);
                Assert(0, iso <> fail);
                # try to adjust by scalar to make iso fix form.
                if quad then
                    got := false;
                    mat := iso * form * TransposedMat(iso);
                    for i in [2..d] do
                        for j in [1..i-1] do
                            mat[j,i] := mat[j,i] + mat[i,j];
                            if mat[j,i] <> Zero(GF(q)) and not got then
                                scal := mat[j,i] * form[j,i]^-1;
                                got := true;
                            fi;
                            mat[i,j] := 0*mat[i,j];
                        od;
                    od;
                else
                    scal := (iso * form * TransposedMat(iso) * form^-1)[1,1];
                fi;
                v := RootFFE(GF(q), scal, 2);
                if v <> fail then
                    iso := iso * (v^-1 * IdentityMat(d, GF(q)));
                elif not normaliser then
                    continue;
                fi;
                det := DeterminantMat(iso);
                if det = (-1)*One(GF(q)) and IsOddInt(d) then
                    iso := iso * ((-1)*One(GF(q)) * IdentityMat(d, GF(q)));
                elif not general and det <> One(GF(q)) then
                    continue;
                fi;
                iso := tmat^-1 * iso * tmat;
                if not special then
                    if (forms.formType = "orthogonalplus" and not CM_InOmega(iso, d, q, 1)) or
                        (forms.formType = "orthogonalminus" and not CM_InOmega(iso, d, q, -1)) then
                        if IsOddInt(q) and not dsq then
                            iso := -iso;
                        else
                            continue;
                        fi;
                    fi;
                    if forms.formType = "orthogonalcircle" and not CM_InOmega(iso, d, q, 0) then
                        continue;
                    fi;
                fi;
                # We will try to make the order of iso as small as possible.
                # if normaliser is true, we will sacrifice fixing form if necessary
                projectiveOrderIso := ProjectiveOrder(iso);
                po := projectiveOrderIso[1];  # iso^po = xI
                x := projectiveOrderIso[2];
                ox := Order(x);
                if special and ox > 1 then
                    f := PrimePowersInt(ox);
                    f := List([1..Length(f)/2], i -> [f[2*i-1], f[2*i]]);
                    ff := List(f, x -> ox / x[1]^x[2]);
                    co := GcdRepresentation(ff);
                    for k in [1..Size(f)] do
                        u := x^(co[k] * ff[k]);  # factor of x with order f[k,1]^f[k,2]
                        rts := RootsOfUPol(GF(q), X(GF(q))^po - u);
                        if rts <> [] then
                            got := false;
                            for v in rts do
                                if v = (-1)*One(GF(q)) and IsEvenInt(d) and IsOddInt(q) then
                                    # v * I_d has det 1
                                    iso := iso * (v^-1 * IdentityMat(d, GF(q)));
                                    got := true;
                                    break;
                                fi;
                            od;
                            if normaliser and not got then
                                iso := iso * (rts[1]^-1 * IdentityMat(d, GF(q)));
                            fi;
                        fi;
                    od;
                fi;
                Add(gens, iso);
            od;
            # finally adjoin scalars
            if normaliser and q > 2 then
                Add(gens, w * IdentityMat(d, GF(q)));
            elif (general and IsOddInt(q)) or (special and IsEvenInt(d) and IsOddInt(q)) or
                (forms.formType = "symplectic" or (IsEvenInt(d) and dsq)) then
                Add(gens, ((-1)*One(GF(q))) * IdentityMat(d, GF(q)));
            fi;
            if normaliser then
                Add(gps, GroupByGenerators(gens));
            else
                Add(gps, ConjugateToStandardForm(GroupByGenerators(gens), type, GF(q)));
            fi;
        fi;
    od;
    return gps;
end);
