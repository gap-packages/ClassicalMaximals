#
# ClassicalMaximals: Maximal subgroups of classical groups
#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage( "ClassicalMaximals" );

# This has to be bound to any value to run the broken tests
CLASSICAL_MAXIMALS_RUN_BROKEN_TESTS := 1;

ReadPackage( "ClassicalMaximals", "tst/utils.g" );
TestDirectory(DirectoriesPackageLibrary( "ClassicalMaximals", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error
