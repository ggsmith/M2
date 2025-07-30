newPackage(
    "GroebnerAlgebras",
    Version => "0.1",
    Date => "30 July 2025",
    Headline => "routines related to non-commutative rings with good Groebner theory",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    Keywords => {"Noncommutative Algebra"},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {}

-* Code section *-


-* Documentation section *-
beginDocumentation()

///
Key
  GroebnerAlgebras
Headline
  routines related to non-commutative rings with good Groebner theory
Description
  Text
  Example
    1+1 == 2
SeeAlso
///

///
Key
Headline
Usage
Inputs
Outputs
Description
  Text
  Example
SeeAlso
///

-* Test section *-
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
///

end--

-* Development section *-
restart
debug needsPackage "GroebnerAlgebras"
check "GroebnerAlgebras"

uninstallPackage "GroebnerAlgebras"
restart
installPackage "GroebnerAlgebras"
viewHelp "GroebnerAlgebras"
