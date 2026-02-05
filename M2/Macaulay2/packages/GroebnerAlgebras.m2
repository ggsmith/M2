-- TODOs (created 15 Dec 2025)
-- Next up (in 2026): get arithmetic working for these rings, in the engine.
-- 1. complementOkay in matrix2.m2 should disallow Groebner Algebras?  Or sometimes?
-- 2. our makeGroebnerAlgebra doesn't allow quotients yet.
-- 3. We don't allow the base to be a polynomial ring (i.e. towers not handled).
newPackage(
    "GroebnerAlgebras",
    Version => "0.2",
    Date => "13 January 2026",
    Headline => "routines related to non-commutative rings with good Groebner theory",
    Authors => {
        { Name => "Michael K. Brown",
            Email => "mkb0096@auburn.edu",
            HomePage => "https://webhome.auburn.edu/~mkb0096/"},
        {  Name => "Michael Perlman", 
            Email => "mperlman@ua.edu", 
            HomePage => "https://sites.google.com/view/michaelperlman/home"},
        { Name => "Gregory G. Smith", 
            Email => "ggsmith@mast.queensu.ca", 
            HomePage => "http://www.mast.queensu.ca/~ggsmith"},
        {  Name => "Michael Stillman",
            Email => "mes15@cornell.edu",
            HomePage => "https://mikestillman.github.io"}
        },
    Keywords => {"Noncommutative Algebra"},
    PackageExports => {"AssociativeAlgebras"}, -- temporary
    AuxiliaryFiles => false,
    DebuggingMode => true
    )

export {
    "groebnerAlgebra",
    "quantumPolynomialRing",
    "toAssociativeAlgebra",
    "associativeEquations",
    "vZeroWeylAlgebra",
    "weylAlgebra",
    "GroebnerAlgebra",
    "homogeneousCliffordAlgebra",
    "isGroebnerAlgebra"
    }

exportFrom_Core {
    "BaseRing",
    "commonEngineRingInitializations",
    "degreePad",
    "generatorExpressions",
    "generatorSymbols",
    "indexStrings",
    "indexSymbols",
    "liftDegree",
    "makepromoter",
    "numallvars",
    "promoteDegree",
    "raw",
    "rawCoefficient",
    "rawGroebnerAlgebra",
    "rawPairs",
    "rawPromote",
    "RawRing"
    }

-- TODO next time: get this functional, probably in GroebnerAlgebras.m2
GroebnerAlgebra = new Type of PolynomialRing
GroebnerAlgebra.synonym = "Groebner algebra"
GroebnerAlgebra#AfterPrint = R -> (
    class R
    -- if #R.monoid.Options#GroebnerAlgebra > 0
    -- then (", ", " with ...")
    )

isGroebnerAlgebra = method()
isGroebnerAlgebra Ring := Boolean => R -> false
isGroebnerAlgebra QuotientRing := Boolean => R -> isGroebnerAlgebra ambient R
isGroebnerAlgebra GroebnerAlgebra := Boolean => R -> true

-- private function which does the work of Ring Array
makeGroebnerAlgebra = method()
makeGroebnerAlgebra(Matrix, Matrix, List) := (C, D, sqIndices) -> (
    -- TODO: want to allow the coefficient ring R to be a polynomial ring, this means
    -- distinguishing between Monoid and FlatMonoid.
    GA := new GroebnerAlgebra from rawGroebnerAlgebra(raw C, raw D, sqIndices); -- RM below ==> GA
    R := coefficientRing ring D;
    M := monoid ring D;
    F := M; -- will be the flat monoid, once we allow this
    nvars := numgens M;
    GA.isCommutative = false;
    GA.monoid     = M;
    GA.FlatMonoid = F;
    GA.BaseRing   = R;
    GA.char       = R.char;
    GA.baseRings  = append(R.baseRings, R);
    GA.numallvars = nvars;
    GA.cache      = new CacheTable;
    GA.cache.GroebnerAlgebra = {C, D};
    -- degree promote and lift
    -- warning: the following two functions must be defined before something below,
    --   otherwise (for example) matrix promotion fails due to mismatched degrees.
    --   Not sure why yet!
    GA.promoteDegree = (
	if F.Options.DegreeMap === null
	then makepromoter degreeLength GA -- means the degree map is zero
	else (
	    dm := F.Options.DegreeMap;
	    nd := F.Options.DegreeRank;
	    degs -> apply(degs, deg -> degreePad(nd, dm deg))
            )
        );
    GA.liftDegree = (
	if F.Options.DegreeLift === null
	then makepromoter degreeLength R -- lifing the zero degree map
	else (
	    lm := F.Options.DegreeLift;
	    degs -> apply(degs, lm)
            )
        );
    GA.generators = apply(nvars, i -> GA_i);
    GA.generatorSymbols     = M.generatorSymbols;
    GA.generatorExpressions = M.generatorExpressions;
    -- degrees
    GA.degreesRing   = F.degreesRing;
    GA.degreesMonoid = F.degreesMonoid;
    -- indexes of variables
    GA.index        = hashTable apply(GA.generatorSymbols, 0 ..< nvars,  identity);
    GA.indexSymbols = hashTable join(
	apply(if R.?indexSymbols then pairs R.indexSymbols else {},
	    (sym, x) -> sym => new GA from rawPromote(raw GA, raw x)),
	apply(GA.generatorSymbols, GA.generators, identity)
	);
    GA.indexStrings = applyKeys(GA.indexSymbols, toString);
    -- coefficients of a monomial
    GA _ M := (f,m) -> new R from rawCoefficient(R.RawRing, raw f, raw m);
    -- for printing
    processMons := (coeffs, monoms) -> if #coeffs === 0 then expression 0 else sum(coeffs, monoms,
	(c, m) -> expression(if c == 1 then 1 else promote(c, R)) * expression(new M from m));
    expression GA := f -> processMons rawPairs(raw R, raw f);
    -- promotions
    commonEngineRingInitializations GA; -- TODO next time: to be tested.
    return GA;
    -----------------------------------------------------------------------------
    -- if R#?"has quotient elements" or isQuotientOf(PolynomialRing, R) then (
    --     RM.RawRing = rawQuotientRing(RM.RawRing, R.RawRing);
    --     RM#"has quotient elements" = true);
    )

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
    GA := makeGroebnerAlgebra(matC, matD, sqIndices);
    return GA
    )

isWellDefined GroebnerAlgebra := Boolean => A -> (
    -- what we need to check:
    -- - for all i,j, lead term of dij  < lead term of xi*xj (in the order on S).
    -- - non-degeneracy condition: should be that associativity holds in A.
    --     see https://www.singular.uni-kl.de/Manual/latest/sing_497.htm#SEC537
    -- - do the cij's needs to be units?
    )

-- XXX
toAssociativeAlgebra = method()
toAssociativeAlgebra GroebnerAlgebra := Ideal => G -> (
  A := QQ<|reverse gens ring last G.cache.GroebnerAlgebra|>;
  (C, D) := toSequence G.cache.GroebnerAlgebra;
  D' := substitute(D, A);
  nA := numgens A;
  I1 := ideal flatten for i from 0 to numgens A - 1 list for j from i+1 to numgens A - 1 list (
      A_(nA-1-j) * A_(nA-1-i) - C_(i,j) * A_(nA-1-i) * A_(nA-1-j) - D'_(i,j)
      );
  I2 := ideal for i from 0 to numgens A - 1 list (
      if D'_(i,i) == 0 then continue else A_(nA-1-i)^2 - D'_(i,i)
      );
  I := I1 + I2;
  I
  )

associativeEquations = method()
associativeEquations GroebnerAlgebra := List => GA -> (
    associativeEquations toAssociativeAlgebra GA;
    )
associativeEquations Ideal := List => I -> (
    -- I is the result of toAssociativeAlgebra.
    R := ring I;
    gbI := NCGB(I, 10);
    triples := subsets(gens R, 3);
    for t in triples list (
        (a,b,c) := toSequence t;
        try1 := NCReductionTwoSided(NCReductionTwoSided(a*b, gbI) * c, gbI);
        try2 := NCReductionTwoSided(a * NCReductionTwoSided(b*c, gbI), gbI);
        try1 - try2
        )
    )

-*
restart
needsPackage "GroebnerAlgebras"
*-
TEST ///
  S = QQ[x_0..x_3]
  L = {x_0^2, x_1^2}
  GA = homogeneousCliffordAlgebra L
  I = toAssociativeAlgebra GA
  assert all(associativeEquations I, f -> f == 0)
///

-*
restart
needsPackage "GroebnerAlgebras"
*-
TEST ///
  S = QQ[x_0..x_2]
  C = hashTable {
      (0,1) => 2_QQ,
      (0,2) => 2_QQ,
      (1,2) => 2_QQ
      }
  D = hashTable {
      (0,1) => x_0 + x_1 + x_2,
      (0,2) => x_0 + x_1 + x_2,
      (1,2) => x_0 + x_1 + x_2
      }
  GA = groebnerAlgebra(C, D)
  I = toAssociativeAlgebra GA
  I_2
  (x_2 * x_1) * x_0 - I_2 * x_0
  
XXX  f21 * x_0
  
  associativeEquations I
  
///


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
  -- TODO: this test fails
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
-- XXX
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  R = QQ[x_0, x_1];
  Cl = homogeneousCliffordAlgebra({x_0^2, x_1^2})

  assert(coefficientRing Cl === QQ)
  assert(char Cl === 0)
  assert(baseRing Cl === QQ)
  assert(numgens Cl === 4)
  assert(Cl.baseRings === {ZZ, QQ})
  assert(numgens degreesRing Cl === 1)
  assert(numgens degreesMonoid Cl  === 1)
  assert(degree t_1 === {1})
  assert(index t_1 === 0)
  assert(index t_2 === 1)
  assert(index e_0 === 2)
  assert(index e_1 === 3)
  assert(index(2*e_1) === null)
  1_Cl == 1
  2_Cl == 2
  assert(ring 2_Cl === Cl)
  -- (2_Cl)^3 -- not functional yet
  assert(3 == (t_1 + t_1 + t_1)_(t_1))

  a = promote(1/3, Cl)
  assert(a === (1/3)_Cl)
  assert(lift((1/3)_Cl, QQ) === 1/3)

  a = promote(3, Cl)
  assert(a === 3_Cl)
  assert(lift(3_Cl, ZZ) === 3)
  assert liftable(3_Cl, ZZ)
  assert not liftable((1/3)_Cl, ZZ)

  m = matrix{{Cl_0+Cl_1, Cl_1 + 1}}
  isHomogeneous m
  degrees source m
  degrees target m

  m = matrix {{1,2},{3,5/2}}
  mCl = promote(m, Cl)
  mQQ = lift(mCl, QQ)
  assert(m == mQQ)
///

-*
-- XXX
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  -- xj * xi = cij * xi * xj + dij, j > i.
  -- Let's compute the Associative Algebra of a Groebner Algebra.
  R = QQ[x_0, x_1];
  Cl = homogeneousCliffordAlgebra({x_0^2, x_1^2})
  Cl.cache.GroebnerAlgebra
  needsPackage "AssociativeAlgebras"
  A = QQ<|reverse gens ring last Cl.cache.GroebnerAlgebra, Degrees => {1,1,2,2}|>
  (C, D) = toSequence Cl.cache.GroebnerAlgebra
  D' = substitute(D, A)
  ring C
  nA = numgens A
  I1 = ideal flatten for i from 0 to numgens A - 1 list for j from i+1 to numgens A - 1 list (
      A_(nA-1-j) * A_(nA-1-i) - C_(i,j) * A_(nA-1-i) * A_(nA-1-j) - D'_(i,j)
      )
  I2 = ideal for i from 0 to numgens A - 1 list (
      if D'_(i,i) == 0 then continue else A_(nA-1-i)^2 - D'_(i,i)
      )
  I = I1 + I2
  see I
  NCGB(I, 10)
  see ideal oo
  ideal(t_2 * t_1 + t_1 * t_2,
      e_0 * t_1 + t_1 * e_0,
      e_1 * t_1 + t_1 * e_1,

  K = ideal(e_1 * e_0 - e_0 * e_1, e_0^2 - 4*t_1, e_1^2 - 4*t_2)
  NCGB(K, 5)
///

-*
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  -- xj * xi = cij * xi * xj + dij, j > i.
  -- Let's compute the Associative Algebra of a Groebner Algebra.
  R = QQ[x_0, x_1];
  Cl = homogeneousCliffordAlgebra({x_0^2, x_1^2})
  I = toAssociativeAlgebra Cl
  ideal NCGB(I, 10) -- TODO: need a test here...
///

-*
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  -- xj * xi = cij * xi * xj + dij, j > i.
  -- Let's compute the Associative Algebra of a Groebner Algebra.
  R = QQ[x_0, x_1];
  Cl = homogeneousCliffordAlgebra({x_0^2, x_1^2})
  I = toAssociativeAlgebra Cl
  ideal NCGB(I, 10) -- TODO: need a test here...
///

-*
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  -- xj * xi = cij * xi * xj + dij, j > i.
  -- Let's compute the Associative Algebra of a Groebner Algebra.
  R = QQ[x_0, x_1, x_2];
  Cl = homogeneousCliffordAlgebra({x_0^2, x_1^2, x_2^2})
  I = toAssociativeAlgebra Cl
  ideal NCGB(I, 10) -- TODO: need a test here...
///

-*
  restart
  needsPackage "GroebnerAlgebras"
*-
TEST ///
  K = frac(QQ[c,d,e,f])
  R = K<| y, x |>
  I = ideal(y*x - c*x*y - d*x - e*y - f)
  NCReductionTwoSided(y*x, I)
  NCReductionTwoSided(y^2*x, I)
  NCReductionTwoSided(y*x^2, I)
  I = ideal(y*x - c*x*y - d*x - e*y - f)
///

-*
  restart
  needsPackage "GroebnerAlgebras"
  -- XXX This is the example of noncommutative P2's we worked on on 4 Feb 2026.
*-
TEST ///
  K = QQ[c_(0,1), c_(0,2), c_(1,2),
          d_(0,1,0), d_(0,1,1), d_(0,1,2), e_(0,1),
          d_(0,2,0), d_(0,2,1), d_(0,2,2), e_(0,2),
          d_(1,2,0), d_(1,2,1), d_(1,2,2), e_(1,2)]
  R = K<| x_2, x_1, x_0 |>
  I = ideal(x_1*x_0 - c_(0,1) * x_0*x_1 - d_(0,1,0) * x_0 - d_(0,1,1) * x_1 - d_(0,1,2) * x_2 - e_(0,1),
      x_2*x_0 - c_(0,2) * x_0*x_2 - d_(0,2,0) * x_0 - d_(0,2,1) * x_1 - d_(0,2,2) * x_2 - e_(0,2),
      x_2*x_1 - c_(1,2) * x_1*x_2 - d_(1,2,0) * x_0 - d_(1,2,1) * x_1 - d_(1,2,2) * x_2 - e_(1,2))
  see I

  f10 = I_0
  f20 = I_1
  f21 = I_2

  g210 = (x_2*x_1*x_0 - f21 * x_0 - c_(1,2) * x_1 * f20 - c_(0,2)*c_(1,2) * f10 * x_2
      - d_(1,2,2) * f20 - (c_(1,2) * d_(0,2,0) + d_(1,2,1)) * f10
      )

  g210' = (x_2*x_1*x_0 - x_2 * f10 - c_(0,1) * f20 * x_1 - c_(0,1) * c_(0,2) * x_0 * f21
      - (c_(0,1) * d_(0,2,2) + d_(0,1,1)) * f21
      - d_(0,1,0) * f20
      )
  g210 - g210'
  (terms oo)/leadCoefficient
  J = ideal for f in oo list sub(f, K)

  see J
  elapsedTime compsJ = decompose J;

  Jc = ideal(c_(1,2))
  positions(compsJ, i -> not isSubset(ideal(c_(1,2) * c_(0,1) * c_(0,2)), i))
  compsJ1 = compsJ_oo
  see compsJ1_0

  netList compsJ1
  -- this one is pretty easy.
  eliminate(compsJ1_0, {d_(1,2,2), c_(0,1), d_(0,2,0)})
  eliminate(compsJ1_0, {c_(0,1), d_(0,1,0), d_(0,2,0), d_(0,1,1)})

  --
  see compsJ1_1
  eliminate(compsJ1_1, {c_(0,1), c_(0,2), c_(1,2)})

  --
  see compsJ1_2
  eliminate(compsJ1_2, {d_(1,2,0), d_(0,2,1),d_(0,2,0) })
  
  see compsJ1_3
  eliminate(compsJ1_3, {d_(1,2,0), d_(0,1,2), d_(0,1,0), c_(0,1)})
  phi = map(K, K, {c_(1,2) => c_(1,2) + 1, c_(0,2) => c_(0,2) + 1})
  eliminate(compsJ1_3, {d_(1,2,0), d_(0,1,2), d_(0,1,0), c_(0,1)})
  L3 = phi oo
  res L3
  see oo

  see compsJ1_4
  eliminate(compsJ1_4, {d_(0,2,1), d_(0,1,2), d_(0,1,1)})
  see oo
  codim compsJ1_4

  see compsJ1_5
///

///
  -- this is perhaps no longer relevant.
  H = new MutableHashTable
  H#(1,0) = x_1*x_0 - I_0
  H#(2,1) = x_2*x_1 - I_2
  H#(2,0) = x_2*x_0 - I_1

  H#(0,2,1) = x_0 * H#(2,1)
  H#(1,0,2) = H#(1,0) * x_2
  H#(2,0,1) = H#(2,0) * x_1 - c_(0,2) * H#(0,2,1) - d_(0,2,2) * H#(1,2)
  
  NCReductionTwoSided(x_2 * x_1, I) * x_0
  F1 = NCReductionTwoSided(oo, I)
  x_2 * NCReductionTwoSided(x_1 * x_0, I)
  F2 = NCReductionTwoSided(oo, I)
  F1 - F2

  lin01 =  d_(0,1,0) * x_0 + d_(0,1,1) * x_1 + d_(0,1,2) * x_2 + e_(0,1)
  lin02 =  d_(0,2,0) * x_0 + d_(0,2,1) * x_1 + d_(0,2,2) * x_2 + e_(0,2)
  lin12 =  d_(1,2,0) * x_0 + d_(1,2,1) * x_1 + d_(1,2,2) * x_2 + e_(1,2)
  assocCond = (c_(0,2) * c_(1,2) * lin01 * x_2 - x_2 * lin01 +
      c_(1,2) * x_1 * lin02 - c_(0,1) * lin02 * x_1 +
      lin12 * x_0 - c_(0,1) * c_(0,2) * x_0 * lin12)
  J = I + ideal(assocCond)
  assert(NCReductionTwoSided(assocCond, I) == F1 - F2)
  G = NCReductionTwoSided(assocCond, I)
  (mons, cfs) = coefficients G
  L = ideal cfs
  lift(L, coefficientRing R)
  lift(oo, ring numerator 1_R)
  leadCoefficient G
  leadTerm G
  NCGB(J, )

  S = ring numerator 1_K
  L = ideal(c_(0,2)*c_(1,2)*d_(0,1,2)-d_(0,1,2),
      c_(0,2)*c_(1,2)*d_(0,1,1)-c_(0,1)*c_(1,2)*d_(0,2,2)-c_(1,2)*d_(0,1,1)+c_(1,2)*d_(0,2,2),
      -c_(0,1)*d_(0,2,1)+c_(1,2)*d_(0,2,1),
      c_(0,2)*c_(1,2)*d_(0,1,0)-c_(0,1)*c_(0,2)*d_(1,2,2)-c_(0,2)*d_(0,1,0)+c_(0,2)*d_(1,2,2),
      c_(0,1)*c_(1,2)*d_(0,2,0)-c_(0,1)*c_(0,2)*d_(1,2,1)-c_(0,1)*d_(0,2,0)+c_(0,1)*d_(1,2,1),
      -c_(0,1)*c_(0,2)*d_(1,2,0)+d_(1,2,0),
      c_(0,2)*c_(1,2)*e_(0,1)+c_(1,2)*d_(0,1,2)*d_(0,2,0)-
        c_(0,1)*d_(0,2,2)*d_(1,2,2)-d_(0,1,0)*d_(0,2,2)+
        d_(0,1,2)*d_(1,2,1)-d_(0,1,1)*d_(1,2,2)+d_(0,2,2)*d_(1,2,2)-e_(0,1),
      c_(1,2)*d_(0,1,1)*d_(0,2,0)-c_(0,1)*d_(0,2,2)*d_(1,2,1)-d_(0,1,0)*d_(0,2,1)-c_(0,1)*e_(0,2)+c_(1,2)*e_(0,2)+d_(0,2,1)*d_(1,2,2),
      c_(1,2)*d_(0,1,0)*d_(0,2,0)-c_(0,1)*d_(0,2,2)*d_(1,2,0)-
        c_(0,1)*c_(0,2)*e_(1,2)-d_(0,1,0)*d_(0,2,0)-d_(0,1,1)*d_(1,2,0)+
        d_(0,1,0)*d_(1,2,1)+d_(0,2,0)*d_(1,2,2)+e_(1,2),
      c_(1,2)*e_(0,1)*d_(0,2,0)-c_(0,1)*d_(0,2,2)*e_(1,2)-d_(0,1,0)*e_(0,2)+e_(0,1)*d_(1,2,1)+e_(0,2)*d_(1,2,2)-d_(0,1,1)*e_(1,2)
      )

  factor L_0
  factor L_1
  factor L_2
  factor L_3
  netList for f in L_* list factor f
  -- 

  R = QQ<| y, x |>
  I = ideal(y*x - 3*x*y - 7*x - 2*y - 4)
  NCGB(I, 10)
  N(y^3*x^3)

  -- for simple example which is not associative
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

-- in the engine.
