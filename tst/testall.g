#
# ClassicalMaximals: Maximal subgroups of classical groups
#
# This file runs package tests.
#
LoadPackage( "ClassicalMaximals" );

ReadPackage( "ClassicalMaximals", "tst/utils.g" );
TestDirectory(DirectoriesPackageLibrary( "ClassicalMaximals", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error
