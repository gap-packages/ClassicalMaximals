#
# ClassicalMaximals: Maximal subgroups of classical groups
#
DeclareInfoClass("InfoClassicalMaximalsTests");

#! @Chapter Maximal Subgroups of Classical Groups

#! @Section The Main function

#! @Arguments type, n, q[, classes]
#! @Description
#! Return representatives of the conjugacy classes of maximal subgroups of
#! the classical group with the given parameters. Here, <A>type</A> must be
#! a string equal to one of <C>"L"</C>, <C>"U"</C>, <C>"S"</C>, <C>"O-"</C>,
#! <C>"O"</C>, or <C>"O+"</C>.
#!
#! The optional argument <A>classes</A> must be a subset of the range <C>[1..9]</C>,
#! corresponding to the Aschbacher classes C1 to C9. If given, it restricts
#! which classes of maximal subgroups are computed.
DeclareGlobalFunction("ClassicalMaximalsGeneric");
# TODO: gap-system/gap has a ClassicalMaximals function. That one should be
# renamed to something like ClassicalMaximalsFromStoredData, then here we
# could drop the -Generic suffix

DeclareGlobalFunction("MaximalSubgroupClassRepsSpecialLinearGroup");
DeclareGlobalFunction("MaximalSubgroupClassRepsSpecialUnitaryGroup");
DeclareGlobalFunction("MaximalSubgroupClassRepsSymplecticGroup");
DeclareGlobalFunction("MaximalSubgroupClassRepsOrthogonalGroup");

DeclareGlobalFunction("GLMinusSL");
DeclareGlobalFunction("GUMinusSU");
DeclareGlobalFunction("NormSpMinusSp");
DeclareGlobalFunction("SOMinusOmega");
DeclareGlobalFunction("GOMinusSO");
DeclareGlobalFunction("NormGOMinusGO");
