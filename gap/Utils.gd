#! @Chapter Utility Functions
#! @Section Matrix Functions
#! @Arguments field, nrRows, nrCols, entries
#! @Description
#! Return a <A>nrRows</A> by <A>nrCols</A> matrix with entries over the field
#! <A>field</A> which are given by the list <A>entries</A> in the following
#! way: If <A>entries</A> is a list of three-element lists <C>[i, j, a]</C>,
#! then the entry in position <C>(i, j)</C> will be set to <C>a</C> (and to
#! zero if <A>entries</A> does not contain a list <C>[i, j, a]</C> with some
#! arbitrary <C>a</C>); if this is not the case and <A>entries</A> is a list of
#! length <C>nrRows * nrCols</C>, the elements of <A>entries</A> will be
#! written into the matrix row by row.
DeclareGlobalFunction("MatrixByEntries");

DeclareGlobalFunction("AntidiagonalMat");
DeclareGlobalFunction("SolveQuadraticCongruence");
DeclareGlobalFunction("ApplyFunctionToEntries");
DeclareGlobalFunction("HermitianConjugate");
DeclareGlobalFunction("SolveFrobeniusEquation");
DeclareGlobalFunction("SquareSingleEntryMatrix");
DeclareGlobalFunction("QuoCeil");
DeclareGlobalFunction("GeneratorsOfOrthogonalGroup");

#! @Chapter Utility Functions
#! @Section Creating Matrix Groups
#! @Arguments gens, F
#! @Description
#! Return a matrix group <C>G</C> over the field <A>F</A> generated by the matrices from
#! the list <A>gens</A>; the generators of <C>G</C> are immutable matrices over
#! <A>F</A>. The attribute <Ref Attr="DefaultFieldOfMatrixGroup"/> for the matrix
#! group constructed will be <A>F</A> (provided <A>F</A> is a finite field of
#! <C>size < 256</C>).
DeclareGlobalFunction("MatrixGroup");
#! @Chapter Utility Functions
#! @Section Creating Matrix Groups
#! @Arguments gens, F, size
#! @Description
#! Return a matrix group over the field <A>F</A> generated by the matrices from
#! the list <A>gens</A> and set its size to <A>size</A>. Except for aditionally
#! setting the group's size, this does the same as <Ref Func="MatrixGroup"/>.
DeclareGlobalFunction("MatrixGroupWithSize");

DeclareGlobalFunction("SizeSp");
DeclareGlobalFunction("SizePSp");
DeclareGlobalFunction("SizeSU");
DeclareGlobalFunction("SizePSU");
DeclareGlobalFunction("SizeGU");
DeclareGlobalFunction("SizeGO");
DeclareGlobalFunction("SizeSO");
