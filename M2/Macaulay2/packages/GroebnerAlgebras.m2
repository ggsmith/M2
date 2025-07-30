newPackage(
    "GroebnerAlgebras",
    Version => "0.1",
    Date => "",
    Headline => "",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    Keywords => {""},
    AuxiliaryFiles => false,
    DebuggingMode => false
    )

export {}

-* Code section *-


-* Documentation section *-
beginDocumentation()

doc ///
Key
  GroebnerAlgebras
Headline
Description
  Text
  Tree
  Example
  CannedExample
Acknowledgement
Contributors
References
Caveat
SeeAlso
Subnodes
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
  Item
Description
  Text
  Example
  CannedExample
  Code
  Pre
ExampleFiles
Contributors
References
Caveat
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
