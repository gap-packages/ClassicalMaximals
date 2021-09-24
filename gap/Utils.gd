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

DeclareGlobalFunction("SizeSp");
DeclareGlobalFunction("SizePSp");
DeclareGlobalFunction("SizeSU");
DeclareGlobalFunction("SizeGU");
DeclareGlobalFunction("SizeGO");
DeclareGlobalFunction("SizeSO");
