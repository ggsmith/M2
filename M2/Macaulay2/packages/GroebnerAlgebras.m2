newPackage(
    "GroebnerAlgebras",
    Version => "0.1",
    Date => "06 October 2025",
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

exportFrom_Core { "raw", "rawGroebnerAlgebra" }

-* Code section *-
GroebnerAlgebra = new Type of PolynomialRing

groebnerAlgebra = method()
groebnerAlgebra(HashTable, HashTable) := GroebnerAlgebra => (C, D) -> (
    -- the values of D are elements of a commutative polynomial ring S = R[x0, ..., x_(n-1)]
    -- C has keys (i,j), $0 \le i < j \le n-1$, and its values are all
    -- non-zero elements of the coefficient ring R.
    -- D also has keys (i,j), $0 \le i < j \le n-1$, and its values
    --  are "small" entries in the ring S (typically, linear polynomials).
    --  (i.e. in S, x_i*x_j > all monomials in D#(i,j)).
    -- D can also (optionally) have keys (i,i), whose value is a polynomial in S,
    --  less than xi^2 in the monomial order
    -- Creates the ring A = R<x0, ..., x_(n-1)> with multiplication
    --  x_j * x_i = C#(i,j) * x_i * x_j + D#(i,j)
    --  x_i^2 = D#(i,i)
    -- (where the D#(i,i) and D#(i,j) are considered as elements of A).
    Ss := unique for f in values D list ring f;
    if #Ss != 1 then error "expected all elements of second hash table to be in the same polynomial ring";
    S := Ss#0;
    R := coefficientRing S;
    Rs := unique for f in values C list ring f;
    if #Rs =!= 1 or Rs#0 =!= R then
        error "expected all elements of the first hash table to be in the same coefficient ring";
    if not all(values C, f -> f != 0) then error "expected non-zero elements (in fact units?) of the coefficient rings";

    
    n := numgens S;
    matC := mutableMatrix(R, n, n);
    for kv in pairs C do matC_(kv#0) = kv#1;
    matC = matrix matC;
    matD := mutableMatrix(S, n, n);
    for kv in pairs D do matD_(kv#0) = kv#1;
    matD = matrix matD;
    sqIndices := for i when i < n list if D#?(i,i) then i else continue;
    GA := new PolynomialRing from rawGroebnerAlgebra(raw matC, raw matD, sqIndices); -- RM below ==> GA
    --RM.monoid     = M;
    GA.BaseRing   = R; -- is this needed? Should be R here?
    RM.FlatMonoid = F;
    RM.numallvars = numallvars; -- define this
    RM.baseRings  = append(R.baseRings, R);
    RM.cache      = new CacheTable;
    RM.promoteDegree = (
	if F.Options.DegreeMap === null
	then makepromoter degreeLength RM -- means the degree map is zero
	else (
	    dm := F.Options.DegreeMap;
	    nd := F.Options.DegreeRank;
	    degs -> apply(degs, deg -> degreePad(nd, dm deg))));
    RM.liftDegree = (
	if F.Options.DegreeLift === null
	then makepromoter degreeLength R -- lifing the zero degree map
	else (
	    lm := F.Options.DegreeLift;
	    degs -> apply(degs, lm)));
    --
    if R.?char          then RM.char          = R.char; -- TODO: what ring doesn't have .char?
    if F.?degreesRing   then RM.degreesRing   = F.degreesRing;
    if F.?degreesMonoid then RM.degreesMonoid = F.degreesMonoid;
    RM.isCommutative = RWeyl === {} and MWeyl === {} and not RM.?SkewCommutative;
    -- see enginering.m2
    commonEngineRingInitializations RM;
    -- TODO: what is this?
    RM _ M := (f,m) -> new R from rawCoefficient(R.RawRing, raw f, raw m);
    -- printing
    processMons := (coeffs, monoms) -> if #coeffs === 0 then expression 0 else sum(coeffs, monoms,
	(c, m) -> expression(if c == 1 then 1 else promote(c, R)) * expression(new M from m));
    -- TODO: put in something prettier when there are constants
    expression RM := if constants then f -> toString raw f else f -> processMons rawPairs(raw R, raw f);
    --
    if MOpts.Inverses === true then (
	denominator RM := f -> RM_( - min \ apply(transpose exponents f,x->x|{0}) );
	numerator   RM := f -> f * denominator f);
    -----------------------------------------------------------------------------
    RM.generators           = apply(nvars, i -> RM_i);
    RM.generatorSymbols     = M.generatorSymbols;
    RM.generatorExpressions = M.generatorExpressions;
    --
    RM.index        = hashTable apply(RM.generatorSymbols, 0 ..< nvars,  identity);
    RM.indexSymbols = hashTable join(
	-- FIXME: switching the order of the following two reveals a bug in Schubert2
	apply(if R.?indexSymbols then pairs R.indexSymbols else {},
	    (sym, x) -> sym => new RM from rawPromote(raw RM, raw x)),
	apply(RM.generatorSymbols, RM.generators, identity)
	);
    try RM.indexStrings = applyKeys(RM.indexSymbols, toString); -- no error, because this is often harmless
    GA)


    --return(matC, matD, sqIndices, rawA);
   

    
    -- this calls an engine routine to create the ring
    -- need some aux functions, e.g. promote, lift.  Use WeylAlgebras as a template.  Or AssociativeAlgebras?
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
homogeneousCliffordAlgebra List := L -> (
    --L is a regular sequence of quadratic forms in a polynomial ring S over a field.
    c := #L;
    Ss := unique for i from 0 to c - 1 list ring L#i;
    if #Ss != 1 then error "expected all list elements to be in the same polynomial ring";
    S := Ss#0;
    n := numgens S;
    e := getSymbol "e";
    t := getSymbol "t";
    kk := coefficientRing S;
    newS := kk(monoid[t_1..t_c, e_0..e_(n-1)]);
    --should we have an optional argument that allows the user to change the order of the variables in the clifford algebra?
    X := vars S;
    B := apply(c, i -> sub(diff(transpose(X) * X, L_i), newS));
    --B is a list of c matrices, the symmetric bilinear forms associated to the quadrics in L.
    C := hashTable flatten for i from 0 to n+c-2 list for j from i+1 to n+c-1 list (
	(i, j) => if i < c or j < c then 1_(kk) else -1_(kk)
	);
    D := hashTable flatten for i from 0 to n+c-1 list for j from i to n+c-1 list (
	(i, j) => if i < c or j < c then continue else 2 * (sum apply (c, l -> (B#l)_(i-c,j-c)*newS_l))
	);
    print D;
    --C should be all -1's. D#(i,j) should be 2 * (sum_{l = 1}^c B_l(v_i, v_j)),
    -- where v_s is the s'th standard basis vector.
    groebnerAlgebra(C, D)
    )


-- todo: enveloping algebra of sl(2), or sl(n)
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
  homogeneousCliffordAlgebra L
///

-*
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  debug Core
  rawGroebnerAlgebra -- C, D, which diagonal entries in D we want.
  -- xj * xi = C_ij * xi * xj
  R = QQ[x_0, x_1];
  hCA = homogeneousCliffordAlgebra({x_0^2, x_1^2})
  C = mutableMatrix(QQ, numgens R + 2, numgens R + 2) -- 2 is the length of the list
  for kv in pairs hCA#0 do C_(kv#0) = kv#1
  C = matrix C
  S = hCA#2
  describe S
  D = mutableMatrix(S, numrows C, numcols C)
  for kv in pairs hCA#1 do D_(kv#0) = kv#1
  D = matrix D
  sqIndices = {2,3}
  A = rawGroebnerAlgebra(raw C, raw D, sqIndices)
  
///


-*
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  R = QQ[x_0, x_1];
  retval = homogeneousCliffordAlgebra({x_0^2, x_1^2})

  R = QQ[x_0, x_1];
  retval = homogeneousCliffordAlgebra({x_0^2+x_0*x_1, x_1^2})
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

