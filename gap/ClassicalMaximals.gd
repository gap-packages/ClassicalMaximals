#
# ClassicalMaximals: Maximal subgroups of classical groups
#
#! @Chapter Introduction
#!
#! ClassicalMaximals is a package which does some
#! interesting and cool things
#!
#! @Chapter Maximal Subgroups of Classical Groups
#! @Section The Main function

#! @Arguments type, n, q
#! @Description
#! Return ...
#! The main function..
# gap-system/gap has a ClassicalMaximals function. That one should be renamed
# to something like ClassicalMaximalsFromStoredData, then here we could drop
# the -Generic suffix
DeclareGlobalFunction("ClassicalMaximalsGeneric");

#! @Arguments n, q
#! @Description
#! TODO
DeclareGlobalFunction("MaximalSubgroupClassRepsSpecialLinearGroup");

DeclareGlobalFunction("MaximalSubgroupClassRepsSpecialUnitaryGroup");
