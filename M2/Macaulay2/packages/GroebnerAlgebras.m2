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

export {
    "groebnerAlgebra",
    "weylAlgebra",
    "GroebnerAlgebra"
    }

-* Code section *-
GroebnerAlgebra = new Type of PolynomialRing

groebnerAlgebra = method()
groebnerAlgebra(HashTable, HashTable) := GroebnerAlgebra => (C, D) -> (
    -- the values of D are elements of a commutative polynomial ring S = R[x0, ..., x_(n-1)]
    -- C has keys (i,j), $0 \le i < j \le n-1$, and its values are all
    -- non-zero elements of the coefficient ring R.
    -- D also has keys (i,j), $0 \le i < j \le n-1$, and its values
    -- are "small" entries in the ring S (typically, linear polynomials).
    -- Creates the ring A = R<x0, ..., x_(n-1)> with multiplication
    --  x_j * x_i = C#(i,j) * x_i * x_j + D#(i,j)
    -- (where the D#(i,j) is considered as an element of A).
    Ss := unique for f in values D list ring f;
    if #Ss != 1 then error "expected all elements of second hash table to be in the same polynomial ring";
    S := Ss#0;
    R := coefficientRing S;
    Rs := unique for f in values C list ring f;
    if #Rs =!= 1 or Rs#0 =!= R then
        error "expected all elements of the first hash table to be in the same coefficient ring";
    if not all(values C, f -> f != 0) then error "expected non-zero elements (in fact units?) of the coefficient rings";
    -- this will call an engine routine to create the ring
    -- need some aux functions, e.g. promote, lift.  Use WeylAlgebras as a template.  Or AssociativeAlgebras?
    -- rawGroebnerAlgebra(package up C, D for the engine)
    A := new GroebnerAlgebra;
    return A -- this is wrong!!
    )

isWellDefined GroebnerAlgebra := Boolean => A -> (
    -- what we need to check:
    -- - for all i,j, lead term of dij  < lead term of xi*xj (in the order on S).
    -- - non-degeneracy condition: should be that associativity holds in A.
    --     see https://www.singular.uni-kl.de/Manual/latest/sing_497.htm#SEC537
    -- - do the cij's needs to be units?
    )


-- the function vZeroWeylAlgebra(n,0) below with make the n-th Weyl algebra
weylAlgebra = method()
weylAlgebra PolynomialRing := GroebnerAlgebra => S -> (
    R := coefficientRing S;
    n := numgens S;
    if odd n then error "expected an even number of variables";
    m := n // 2;
    C := hashTable flatten for i from 0 to n-2 list for j from i+1 to n-1 list (
        (i,j) => 1_R
        );
    -- TODO: make D, call groebnerAlgebra.
    C
    )

--Quantum polynomial ring:
-- c_{ij} = c_{ji}^{-1}.
-- Quantum exterior algebra: c_{ij} = c_{ji}^{-1},
-- and squares of generators must be zero
-- (is this a Groebner algebra, by our definition?)


vZeroWeylAlgebra = method()
vZeroWeylAlgebra(ZZ,ZZ) := (n,m) -> (
    -- creates the zeroth piece V^0(D_{n+m}) of the Kashiwara--Malgrange V-filtration of D_{n+m} along V(t_1..t_m)
    -- here, D_{n+m} is the Weyl algebra on n+m variables, x_1..x_n and t_1..t_m
    -- the generators of this algebra are x_1..x_n, dx_1..dx_n, -dt_1*t_1...-dt_m*t_m, t_1..t_m
    -- the relations come from the realization of this algebra as a subalgebra of D_{n+m}
    -- it is common to use the variable s_i for -dt_i*t_i
    -- when m=0, this function returns the Weyl algebra D_n
    -- when m=1, this algebra can be uses to calculate Bernstein--Sato polynomials following Briancon--Maisonobe
    -- when m>=1, this algebra is important in the theory of mixed Hodge modules
    -- the coefficient ring will be QQ
    x:= local x;
    dx:= local dx;
    s:= local s;
    t:= local t;
    S:= QQ[x_1..x_n, dx_1..dx_n, s_1..s_m, t_1..t_m];
    C := hashTable flatten for i from 0 to 2*n+2*m-2 list for j from i+1 to 2*n+2*m-1 list (
	(i,j) => 1_QQ);
    DList := {};
    for i from 0 to 2*n+2*m-2 do (
	for j from i+1 to 2*n+2*m-1 do (
	    if (i<n) and (j==n+i) then DList=append(DList,(i,j) => -1_S)
	    else if (i>=2*n) and (i<2*n+m) and (j==m+i) then DList=append(DList,(i,j) => -t_(i-2*n+1))
	    else DList=append(DList, (i,j) => 0_S)
	    );
	);
    D := hashTable DList;
    -- to do: call groebnerAlgebra
    D
    )
    


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

-*
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  R = QQ[a..d]
  weylAlgebra R
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
