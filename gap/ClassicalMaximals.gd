#
# ClassicalMaximals: Maximal subgroups of classical groups
#
DeclareInfoClass("InfoClassicalMaximalsTests");
DeclareInfoClass("InfoClassicalMaximals");
SetInfoLevel(InfoClassicalMaximals, 1);
DeclareGlobalName("CM_c9lib");

#! @Chapter Maximal Subgroups of Classical Groups
#! @ChapterLabel MaximalSubgroups

#! @Section The Main function

#! @Arguments type, n, q[, classes]
#! @Description
#! Returns a list of representatives of the conjugacy classes of maximal subgroups
#! of the quasisimple classical group of the specified type in dimension <A>n</A>
#! over the finite field $\mathbb{F}_q$.
#!
#! The parameter <A>type</A> must be one of the strings
#! `"L"`, `"U"`, `"O"`, `"O+"`, `"O-"`, corresponding to the quasisimple groups
#! ${\rm SL}_n(q)$, ${\rm SU}_n(q)$, ${\rm Sp}_n(q)$, $\Omega_n(q)$,
#! $\Omega^+_n(q)$ and $\Omega^-_n(q)$, respectively
#! (see Chapter <Ref Chap="Chapter_Theory"/>).
#!
#! The returned subgroups are realized as subgroups of the standard classical group
#! (as returned by the corresponding &GAP; functions), so in particular they preserve
#! our standard classical form
#! (see <Ref Sect="Subsection_Theory:ClassicalGroups:StandardForms"/>).
#!
#! The optional argument <A>classes</A> must be a subset of `[1..9]` and specifies
#! which Aschbacher classes are to be computed.
#! If omitted, all classes ${\cal C}_1, \dots, {\cal C}_9$ are considered.
#!
#! The lists are complete for $n \leq 12$. In dimensions 3 and 4, there is a known
#! exception in class ${\cal C}_1$ for orthogonal types; in these cases a warning
#! is issued via the info class `InfoClassicalMaximals`.
#!
#! For $n > 12$, no completeness guarantee is given. In particular, maximal subgroups
#! in class ${\cal C}_9$ are not included in these cases.
#!
#! The orders of the returned subgroups are precomputed and stored with the groups.
#!
#! Section <Ref Chap="Chapter_Examples"/> provides some illustrations
#! of this function's usage.
DeclareGlobalFunction("ClassicalMaximalsGeneric");
# TODO: gap-system/gap has a ClassicalMaximals function. That one should be
# renamed to something like ClassicalMaximalsFromStoredData, then here we
# could drop the -Generic suffix

DeclareGlobalFunction("MaximalSubgroupClassRepsSpecialLinearGroup");
DeclareGlobalFunction("MaximalSubgroupClassRepsSpecialUnitaryGroup");
DeclareGlobalFunction("MaximalSubgroupClassRepsSymplecticGroup");
DeclareGlobalFunction("MaximalSubgroupClassRepsOrthogonalGroup");

#! @Section Conjugating elements in the ambient classical group
#! In several constructions it is necessary to pass between a classical group
#! and larger groups in which it is naturally embedded, such as the corresponding
#! general linear, unitary, or orthogonal groups, or their normalisers in the
#! general linear group. In particular, one often needs explicit elements that lie
#! outside a given subgroup but still preserve the relevant form (possibly up to scalars).
#! Such elements can be used to conjugate subgroups and to obtain representatives from
#! different conjugacy classes inside the ambient group.
#! The following functions provide explicit elements in the various overgroups
#! of the classical groups considered in this package.

#! @Arguments n q
#! @Returns an element of ${\rm GL}_n(q) \setminus {\rm SL}_n(q)$.
DeclareGlobalFunction("GLMinusSL");

#! @Arguments n q
#! @Returns an element of ${\rm GU}_n(q) \setminus {\rm SU}_n(q)$.
DeclareGlobalFunction("GUMinusSU");

#! @Arguments n q
#! @Returns an element of
#! ${\rm N}_{{\rm GL}_n(q)}({\rm Sp}_n(q)) \setminus {\rm Sp}_n(q)$
#! which preserves our standard symplectic form modulo a scalar.
DeclareGlobalFunction("NormSpMinusSp");

#! @Arguments epsilon n q
#! @Returns an element of
#! ${\rm SO}^\varepsilon_n(q) \setminus \Omega^\varepsilon_n(q)$
#! which preserves our standard orthogonal form
#! (see <Ref Sect="Subsection_Theory:ClassicalGroups:StandardForms"/>).
DeclareGlobalFunction("SOMinusOmega");

#! @Arguments epsilon n q
#! @Returns an element of
#! ${\rm GO}^\varepsilon_n(q) \setminus {\rm SO}^\varepsilon_n(q)$
#! which preserves our standard orthogonal form
#! (see <Ref Sect="Subsection_Theory:ClassicalGroups:StandardForms"/>).
DeclareGlobalFunction("GOMinusSO");

#! @Arguments epsilon n q
#! @Returns an element of
#! ${\rm N}_{{\rm GL}_n(q)}({\rm GO}^\varepsilon_n(q)) \setminus {\rm GO}^\varepsilon_n(q)$
#! which preserves our standard orthogonal form
#! (see <Ref Sect="Subsection_Theory:ClassicalGroups:StandardForms"/>)
#! modulo a scalar.
DeclareGlobalFunction("NormGOMinusGO");

#! @Subsection Warning concerning orthogonal groups of minus type
#! <Ref Func="SOMinusOmega"/>, <Ref Func="GOMinusSO"/> and <Ref Func="NormGOMinusGO"/>
#! are affected by a historical inconsistency in the choice of the
#! invariant bilinear form for orthogonal groups of minus type.
#!
#! For $\varepsilon = -1$ the forms kept invariant by
#! `Omega(-1,n,q)` and `SO(-1,n,q)` need not coincide.
#!
#! Consequently the element returned by `GOMinusSO(-1,n,q)`
#! preserves the form associated with `Omega(-1,n,q)`
#! (our standard orthogonal form, see
#! <Ref Sect="Subsection_Theory:ClassicalGroups:StandardForms"/>)
#! but does **not** necessarily preserve the form associated with `SO(-1,n,q)`
#! (as one would expect from the name).
#!
#! The element returned by `NormGOMinusGO(-1,n,q)` is guaranteed
#! to normalise a group preserving the `Omega` form (our standard orthogonal form).
#!
#! @BeginLogSession
#! gap> q := 5;;
#! gap> G := Omega(-1, 8, q);;
#! gap> H := SO(-1, 8, q);;
#! gap> Display(InvariantBilinearForm(G).matrix);
#!  . . . . . . . 1
#!  . . . . . . 1 .
#!  . . . . . 1 . .
#!  . . . 3 4 . . .
#!  . . . 4 1 . . .
#!  . . 1 . . . . .
#!  . 1 . . . . . .
#!  1 . . . . . . .
#! gap> Display(InvariantBilinearForm(H).matrix);
#!  . 1 . . . . . .
#!  1 . . . . . . .
#!  . . 4 . . . . .
#!  . . . 2 . . . .
#!  . . . . 2 . . .
#!  . . . . . 2 . .
#!  . . . . . . 2 .
#!  . . . . . . . 2
#! gap> MG := InvariantBilinearForm(G).matrix;;
#! gap> MH := InvariantBilinearForm(H).matrix;;
#! gap> a := GOMinusSO(-1, 8, q);;
#! gap> b := NormGOMinusGO(-1, 8, q);
#! gap> a*MG*TransposedMat(a) = MG;
#! true
#! gap> a*MH*TransposedMat(a) = MH;
#! false
#! gap> (G.1^b)*MG*TransposedMat(G.1^b) = MG;
#! true
#! gap> (G.2^b)*MG*TransposedMat(G.2^b) = MG;
#! true
#! @EndLogSession

#! @Chapter Examples
#! The following examples illustrate the use of
#! <Ref Func="ClassicalMaximalsGeneric"/>.
#!
#! Consider the maximal subgroups of ${\rm SU}_5(7)$.
#! These can be obtained directly as follows:
#! @BeginLogSession
#! gap> L := ClassicalMaximalsGeneric("U", 5, 7);
#! [ <matrix group of size 223883102951424 with 6 generators>,
#!   <matrix group of size 32541148684800 with 6 generators>,
#!   <matrix group of size 37298309529600 with 4 generators>,
#!   <matrix group of size 15223799808 with 5 generators>,
#!   <matrix group of size 491520 with 4 generators>,
#!   <matrix group of size 10505 with 2 generators>,
#!   <matrix group of size 276595200 with 4 generators>,
#!   <matrix group of size 660 with 2 generators> ]
#! gap> DefaultFieldOfMatrixGroup(L[1]);
#! GF(7^2)
#! @EndLogSession
#! Note that unitary groups are defined over
#! $\mathbb{F}_{q^2}$, even though they are parametrised by $q$
#! (see <Ref Sect="Subsection_Theory:ClassicalGroups:U"/>).
#!
#! It is often useful to restrict attention to certain Aschbacher classes.
#! For example, the reducible and imprimitive maximal subgroups of
#! ${\rm Sp}_6(9)$ (that is, classes ${\cal C}_1$ and ${\cal C}_2$) can be
#! obtained by specifying the optional argument <A>classes</A>:
#! @BeginLogSession
#! gap> ClassicalMaximalsGeneric("S", 6, 9, [1, 2]);
#! [ <matrix group of size 1626546181017600 with 6 generators>,
#!   <matrix group of size 19835929036800 with 6 generators>,
#!   <matrix group of size 180506954234880 with 3 generators>,
#!   <matrix group of size 2479113216000 with 4 generators>,
#!   <matrix group of size 2239488000 with 4 generators>,
#!   <matrix group of size 679311360 with 3 generators> ]
#! @EndLogSession
#!
#! The groups returned by <Ref Func="ClassicalMaximalsGeneric"/> are
#! realised as subgroups of the corresponding standard classical group
#! and therefore preserve the standard form. This can be verified using
#! the stored invariant forms. For example, consider a maximal subgroup
#! of ${\rm \Omega}^-_8(5)$ in class ${\cal C}_9$:
#!
#! @BeginLogSession
#! gap> G := ClassicalMaximalsGeneric("O-", 8, 5, [9])[1];
#! <matrix group of size 372000 with 2 generators>
#! gap> Display(InvariantBilinearForm(G).matrix);
#!  . . . . . . . 1
#!  . . . . . . 1 .
#!  . . . . . 1 . .
#!  . . . 3 4 . . .
#!  . . . 4 1 . . .
#!  . . 1 . . . . .
#!  . 1 . . . . . .
#!  1 . . . . . . .
#! gap> Display(InvariantBilinearForm(Omega(-1, 8, 5)).matrix);
#!  . . . . . . . 1
#!  . . . . . . 1 .
#!  . . . . . 1 . .
#!  . . . 3 4 . . .
#!  . . . 4 1 . . .
#!  . . 1 . . . . .
#!  . 1 . . . . . .
#!  1 . . . . . . .
#! @EndLogSession
#! The two matrices coincide, confirming that the subgroup preserves our
#! standard orthogonal form.
