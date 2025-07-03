#
# ClassicalMaximals: Maximal subgroups of classical groups
#
# This file contains package meta data. For additional information on
# the meaning and correct usage of these fields, please consult the
# manual of the "Example" package as well as the comments in its
# PackageInfo.g file.
#
SetPackageInfo( rec(

PackageName := "ClassicalMaximals",
Subtitle := "Maximal subgroups of classical groups",
Version := "0.1",
Date := "07/07/2021", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
  rec(
    FirstNames    := "Maximilian",
    LastName      := "Hauck",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "mahauck@rhrk.uni-kl.de",
    #Place         := "Kaiserslautern, Germany",
    #Institution   := "TU Kaiserslautern", # no longer affiliated
  ),
  rec(
    FirstNames    := "Max",
    LastName      := "Horn",
    IsAuthor      := true,
    IsMaintainer  := true,
    Email         := "mhorn@rptu.de",
    #WWWHome       := "https://www.quendi.de/math",
    GitHubUsername:= "fingolfin",
    Place         := "Kaiserslautern, Germany",
    Institution   := "RPTU Kaiserslautern-Landau",
  ),
  rec(
    FirstNames    := "Tristan",
    LastName      := "Pfersdorff",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "tristan.pfersdorff@edu.rptu.de",
    Place         := "Kaiserslautern, Germany",
    Institution   := "RPTU Kaiserslautern-Landau",
  ),
  rec(
    FirstNames    := "Sergio",
    LastName      := "Siccha",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "siccha@mathematik.uni-kl.de",
    #Place         := "Kaiserslautern, Germany",
    #Institution   := "TU Kaiserslautern", # no longer affiliated
  ),
],

SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/gap-packages/ClassicalMaximals",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := "https://gap-packages.github.io/ClassicalMaximals/",
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL      := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),

ArchiveFormats := ".tar.gz",

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "submitted"     for packages submitted for the refereeing
##    "deposited"     for packages for which the GAP developers agreed
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages
##    "other"         for all other packages
##
Status := "dev",

AbstractHTML   :=  "",

PackageDoc := rec(
  BookName  := "ClassicalMaximals",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Maximal subgroups of classical groups",
),

Dependencies := rec(
  GAP := ">= 4.11",
  NeededOtherPackages := [
          ["Forms", ">=1.2.5"],
    ],
  SuggestedOtherPackages := [ ],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

#Keywords := [ "TODO" ],

));


