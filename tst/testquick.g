#
# ClassicalMaximals: Maximal subgroups of classical groups
#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage( "ClassicalMaximals" );

# skip extra tests using group recognition
QUICK_CLASSICAL_MAXIMALS_TESTS:=true;

ReadPackage( "ClassicalMaximals", "tst/utils.g" );
TestDirectory(DirectoriesPackageLibrary( "ClassicalMaximals", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error
