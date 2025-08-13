newPackage(
    "GroebnerAlgebras",
    Version => "0.1",
    Date => "06 August 2025",
    Headline => "routines related to non-commutative rings with good Groebner theory",
    Authors => {{ Name => "Michael K. Brown",
		  Email => "mkb0096@auburn.edu",
		  HomePage => "https://webhome.auburn.edu/~mkb0096/"},
	        {  Name => "Michael Perlman", 
	          Email => "mperlman@ua.edu", 
		  HomePage => "https://sites.google.com/view/michaelperlman/home"},
	        { Name => "Gregory G. Smith", 
                  Email => "ggsmith@mast.queensu.ca", 
                  HomePage => "http://www.mast.queensu.ca/~ggsmith"},
               {  Name => "", Email => "", HomePage => ""}},
    Keywords => {"Noncommutative Algebra"},
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {
    "groebnerAlgebra",
    "quantumPolynomialRing",
    "vZeroWeylAlgebra",
    "weylAlgebra",
    "GroebnerAlgebra",
    "homogeneousCliffordAlgebra"
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


-- this is our first attempt at making the Weyl algebra
-- a newer implementation is below
--weylAlgebra = method()
--weylAlgebra PolynomialRing := GroebnerAlgebra => S -> (
   -- R := coefficientRing S;
   -- n := numgens S;
   -- if odd n then error "expected an even number of variables";
   -- m := n // 2;
   -- C := hashTable flatten for i from 0 to n-2 list for j from i+1 to n-1 list (
       -- (i,j) => 1_R
       -- );
    -- TODO: make D, call groebnerAlgebra.
   -- C
   -- )



vZeroWeylAlgebra = method()
vZeroWeylAlgebra(ZZ,ZZ) := GroebnerAlgebra => (n,m) -> (
    -- creates the zeroth piece V^0(D_{n+m}) of the Kashiwara--Malgrange V-filtration of D_{n+m} along V(t_1..t_m)
    -- here, D_{n+m} is the Weyl algebra on n+m variables, x_1..x_n and t_1..t_m
    -- the generators of this algebra are x_1..x_n, dx_1..dx_n, -dt_1*t_1...-dt_m*t_m, t_1..t_m
    -- the relations come from the realization of this algebra as a subalgebra of D_{n+m}
    -- it is common to use the variable s_i for -dt_i*t_i
    -- when m=0, this function returns the Weyl algebra D_n
    -- when m=1, this algebra can be uses to calculate Bernstein--Sato polynomials following Briancon--Maisonobe
    -- when m>=1, this algebra is important in the theory of mixed Hodge modules
    -- the coefficient ring will be QQ
    x:= getSymbol "x";
    dx:= getSymbol "dx";
    s:= getSymbol "s";
    t:= getSymbol "t";
    S:= QQ[x_1..x_n, dx_1..dx_n, s_1..s_m, t_1..t_m];
    C := hashTable flatten for i from 0 to 2*n+2*m-2 list for j from i+1 to 2*n+2*m-1 list (
        (i,j) => 1_QQ);
    D := hashTable flatten for i from 0 to 2*n+2*m-2 list (
        for j from i+1 to 2*n+2*m-1 list (
            if (i<n) and (j==n+i) then
                (i,j) => -1_S
            else if (i>=2*n) and (i<2*n+m) and (j==m+i) then
                (i,j) => - S_(m+i)
            else
                continue
                --(i,j) => 0_S
            )
        );
    -- to do: call groebnerAlgebra
    (C, D, S)
    )

weylAlgebra = method()
weylAlgebra(ZZ) := GroebnerAlgebra => n -> (
    vZeroWeylAlgebra(n,0)
    )
    
--Quantum polynomial ring:
-- c_{ij} = c_{ji}^{-1}.
-- Quantum exterior algebra: c_{ij} = c_{ji}^{-1},
-- and squares of generators must be zero
-- (is this a Groebner algebra, by our definition?)

quantumPolynomialRing = method()
quantumPolynomialRing Ring := R -> (
    -- R is of the form kk[x_0..x_(n-1)].
    n := numgens R;
    q := getSymbol "q";
    allpairs := subsets(0..(n-1), 2);
    allvars := for ij in allpairs list q_(toSequence ij);
    K := coefficientRing R;
    L := frac(K[allvars]);
    S := L (monoid R);
    D := new HashTable;
    C := hashTable for a from 0 to #allpairs - 1 list (
        ij := toSequence allpairs#a;
        ij => L_a
        );
    (C, D, S)
    )

homogeneousCliffordAlgebra = method()
--The problem here is that a homogeneous Clifford algebra is not a Groebner algebra, by our definition.
--This is because there are relations involving the squares of the generators (i.e. we need diagonal entries
--in our hashtable D).
--One has the same problem with an exterior algebra.
homogeneousCliffordAlgebra (Ring, List) := (S, L) -> (
    --S is of the form kk[x_0..x_(n-1)], where char(k) is not 2;
    --and L is a regular sequence of quadratic forms in S.
    n := numgens S;
    c := #L;
    --vecs := apply(n, i -> entries (id_(S^n))_i); --standard basis vectors, as lists.
    --B := apply(#L, i -> matrix (
    --	      apply(n, j -> (
	       --apply(n, l -> L_i(new Sequence from (vecs_j + vecs_l)) - L_i(new Sequence from vecs_j) - L_i(new Sequence from vecs_l)
		--	)
		   -- )
	--	)
	   -- )
--	);
    e := getSymbol "e";
    t := getSymbol "t";
    kk := coefficientRing S;
    newS := kk(monoid[t_1..t_c, e_0..e_(n-1)]);
    X := vars S;
    B := apply(c, i -> sub(diff(transpose(X) * X, L_i), newS));
    print B;
    C := hashTable flatten for i from 0 to n+c-2 list for j from i+1 to n+c-1 list (
	(i, j) => if i < c or j < c then 1_(kk) else -1_(kk)
	);
    D := hashTable flatten for i from 0 to n+c-2 list for j from i+1 to n+c-1 list (
	(i, j) => if i < c or j < c then 0_(newS) else 2 * (sum apply (c, l -> (B#l)_(i-c,j-c)*newS_l))
	);
    (C, D,S)
    --Can maybe speed up calculation of the list B of bilinear forms by taking appropriate derivatives of the quadrics in L. 
    --B is a list of #L matrices, the symmetric bilinear forms associated to the quadrics in L.
    --C should be all -1's. D#(i,j) should be 2 * (for l from 0 to c-1 sum entries (transpose(matrix{vecs_j})*B_l*matrix{vecs_i})_0)
    )


-- todo: enveloping algebra of sl(2), or sl(n)
--       homogeneous Clifford algebras
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
  W = weylAlgebra(3)

  (C, D, S) = vZeroWeylAlgebra(2, 2)
  describe S
  gens S
  C
///

-*
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  R = QQ[x_0..x_3]
  (C, D, S) = quantumPolynomialRing R
  (values C)/ring
  S = QQ[x_0..x_3]
  L = {x_0^2, x_1^2}
  homogeneousCliffordAlgebra(S, L)
///

-- todo to get groebnerAlgebra up and running:
-- want, e.g: A = groebnerAlgebra(S, C, D) -- C elements are in coeff ring of S, D elements are in S.
--  1. in m2 directory in Macaulay2: m2/polyrings.m2: newWeylAlgebra, Ring Monoid.
--     also: isGroebnerAlgebra, AfterPrint.
--  2. rawWeylAlgebra in Macaulay2/d/interface.dd
--  3. in Macaulay2/e/interface: IM2_Ring_weyl_algebra, IM2_Ring_solvable_algebra.
--      e/interface/ring.cpp, e/interface/ring.h
--  4. in Macaulay2/e/weylalg.hpp, weylalg.cpp: the actual c++ code to do the multiplication (and powers).

end--

-* Development section *-
restart
debug needsPackage "GroebnerAlgebras"
check "GroebnerAlgebras"

uninstallPackage "GroebnerAlgebras"
restart
installPackage "GroebnerAlgebras"
viewHelp "GroebnerAlgebras"

