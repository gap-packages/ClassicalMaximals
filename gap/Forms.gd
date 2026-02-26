DeclareGlobalFunction("ConjugateToSesquilinearForm");
DeclareGlobalFunction("ConjugateToStandardForm");
DeclareGlobalFunction("StandardOrthogonalForm");
DeclareGlobalFunction("CM_UnitaryForm");
DeclareGlobalFunction("CM_BilinearForm");
DeclareGlobalFunction("CM_SymplecticForm");
DeclareGlobalFunction("CM_SymmetricBilinearForm");
DeclareGlobalFunction("CM_QuadraticForm");

#! @Chapter Group Recognition
#! @Section Classical Forms
#! @Arguments G field
#! @Description
#!  Assuming that the matrix group <A>G</A> is acting absolutely irreducibly on a vector
#!  space $V$ over the field <A>field</A>, this function attempts to
#!  determine whether <A>G</A> preserves a classical form on $V$.
#!
#!  The search terminates as soon as a single <A>G</A>-invariant form is identified;
#!  no attempt is made to detect additional invariant forms of other types.
#!
#!  The classical forms considered are:
#!  * **orthogonal**: a symmetric bilinear form together with an associated
#!    quadratic form,
#!  * **symplectic**: a non-degenerate alternating bilinear form,
#!  * **unitary**: a non-degenerate sesquilinear form.
#!
#!  Returns: A record with the following components:
#!  * <C>formType</C>
#!  * <C>bilinearForm</C>
#!  * <C>sesquilinearForm</C>
#!  * <C>quadraticForm</C>
#!  * <C>sign</C> (for orthogonal forms)
#!
#!  The value of <C>formType</C> determines how these components should be interpreted:
#!  * <C>"orthogonalcircle"</C>, <C>"orthogonalplus"</C>, <C>"orthogonalminus"</C>:
#!    <A>G</A> fixes an orthogonal form. The matrix of the associated bilinear form
#!    is given in <C>bilinearForm</C>, and the matrix of the corresponding quadratic
#!    form is given in <C>quadraticForm</C>.
#!    The component <C>sign</C> distinguishes the three orthogonal types, taking the
#!    values:
#!    * <C>0</C> for <C>"orthogonalcircle"</C>,
#!    * <C>1</C> for <C>"orthogonalplus"</C>,
#!    * <C>-1</C> for <C>"orthogonalminus"</C>.
#!  * <C>"symplectic"</C>: <A>G</A> fixes a symplectic form. The form matrix is given
#!    in <C>bilinearForm</C>.
#!  * <C>"unitary"</C>: <A>G</A> fixes a unitary form. The form matrix is given in
#!    <C>sesquilinearForm</C>.
#!  * <C>"linear"</C>: <A>G</A> does not fix any classical form.
DeclareGlobalFunction("CM_ClassicalForms");
DeclareGlobalFunction("ConjugateToStandardFormAutoType");
