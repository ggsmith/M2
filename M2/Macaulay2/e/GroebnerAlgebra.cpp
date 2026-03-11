// Copyright 2025 The Macaulay2 Authors

#include "GroebnerAlgebra.hpp"

#include "gbring.hpp"
#include "ExponentVector.hpp"
#include "geopoly.hpp"
#include "text-io.hpp"
#include "matrix.hpp"
#include "util.hpp"


bool GroebnerAlgebra::initialize_groebner_algebra(const Matrix* C,
                                                  const Matrix* D,
                                                  const std::vector<int>& squaring_indices)
{
  this->mC = C;
  this->mD = D;
  this->mSquaringIndices = squaring_indices;

  return true;
}

GroebnerAlgebra *GroebnerAlgebra::create(const Matrix* C,
                                         const Matrix* D,
                                         M2_arrayint squaring_indices)
{
  const Ring* R = D->get_ring();
  const PolynomialRing *P = R->cast_to_PolynomialRing();
  if (P == nullptr)
    {
      throw exc::engine_error("expected a matrix over a polynomial ring");
    }

  //TODO:  check that C, D squaring_indices all have some basic features correct
  GroebnerAlgebra *result = new GroebnerAlgebra;
  result->initialize_poly_ring(P->getCoefficients(), P->getMonoid());

  std::vector<int> squaring { M2_arrayint_to_stdvector<int>(squaring_indices) };
  
  if (!result->initialize_groebner_algebra(C, D, squaring)) return nullptr;

  //TODO: what is this?   result->gb_ring_ = GBRing::create_GroebnerAlgebra(K, M, weyl);
  return result;
}


void GroebnerAlgebra::text_out(buffer &o) const
{
  o << "GroebnerAlgebra(";
  K_->text_out(o);
  M_->text_out(o);
  o << ")";
}

/////////////////

Nterm* GroebnerAlgebra::mult_by_variable(int v, Nterm* f) const
// v is the integer index of a variable in the GroebnerAlgebra.
// f is a polynomial in normal form as a linked list of Nterm's.
{
  polyheap result(this);

  for (Nterm& t : f)
    {
      // multiply g := xv * t, add it to result.
      // commute the variable xv across the monomial in the term t.
      // monomial t in f:  [i0, i1, i2, i3, ..., ir] where i0 <= i1 <= ...
      // variable v.
      // v > i0: C_** * [i0, v, i1, ...] + D**.
      // result.add(g);
    }
  
  
  return result.value();
}

// TODO: Feb 25, 2026: write these functions.
const Nterm* GroebnerAlgebra::mult_var_var(int v, int w) const
// might want to assume v >= w here.
{
  // Let's make an array Nterm* [][], where the (v,w) entry, for v >= w
  //   is the RHS of x_v * x_w = C_(wv) * x_w *x_v + D_(wv).
  // lookup of the result
  return mMultTable[v][w]; // warning: this is meant to be const.
}
Nterm* GroebnerAlgebra::mult_exp_var(exponents_t a, int j) const
// let i be the last variable of a, a' = a/x_i
// i >= j: mult_exp_poly(a', mult_var_var(i, j))
// i < j: just create a single monomial
{
  Nterm* result = nullptr;
  int i;
  for (i=nvars_ - 1; i >= 0 and a[i] == 0; --i) { }
  if (i == -1)
    {
      // make a into a Nterm* and return it.
    }
  if (i < j)
    {
      a[j]++;
      // convert a to Nterm*
      result = nullptr; //
      a[j]--;
    }
  else
    {
      a[i]--;
      const Nterm* f = mult_var_var(i, j);
      result = mult_exp_poly(a, f);
      a[i]++;
    }
  return result;
}

Nterm* GroebnerAlgebra::mult_exp_poly(exponents_t a, const Nterm* ft) const
//  x^a * ft
// sum of coeff * mult_exp_exp(a, term of ft).
{
}

Nterm* GroebnerAlgebra::mult_poly_exp(const Nterm* ft, exponents_t a) const
//  ft * x^a
// sum of coeff * mult_exp_exp(term of ft, a).
{
}

Nterm* GroebnerAlgebra::mult_exp_exp(exponents_t a, exponents_t b) const
// find the first non-zero element of b, say x_i
// b' = b/x_i
// mult_poly_exp(mult_exp_var(a, i), b')
{
  int i;
  for (i=0; i < nvars_ and b[i] == 0; ++i) { }
  if (i == nvars_)
    {
      // make a into a Nterm* and return it.
    }
  b[i]--;
  Nterm* f = mult_exp_var(a, i);
  Nterm* result = mult_poly_exp(f, b);
  b[i]++;
  return result;
}

Nterm* GroebnerAlgebra::mult_term_term(const Nterm* ft, const Nterm* gt) const
// multiply the terms ft * gt, ft = cf * x^a, gt = cg * x^b.
// need to multiply x^a, x^b, then mult result by cf*cg.
// needs lots of mult_exp_exp's, and mult coefficients to a polynomial.
{
  ring_elem cf = ft->coeff;
  ring_elem cg = gt->coeff;
  exponents_t expf = new int[nvars_];
  exponents_t expg = new int[nvars_];
  M_->to_expvector(ft->monom, expf);
  M_->to_expvector(gt->monom, expg);
  
  Nterm* fg = mult_exp_exp(expf, expg);
  // TODO: find this function!
  //  mult_coeff_to_poly(K_->mult(cf, cg), fg);

  delete [] expf;
  delete [] expg;
  return fg;
}

Nterm* GroebnerAlgebra::mult_poly_poly(const Nterm* f, const Nterm* g) const
// multiply the two polynomials f*g
{
  polyheap result(this);

  for (const Nterm* s = f; s != nullptr; s = s->next)
    for (const Nterm* t = g; t != nullptr; t = t->next)
      {
        Nterm* st = mult_term_term(s, t);
        result.add(st);
      }
  
  return result.value();
}
///////////////////////////////////////////

// ring_elem GroebnerAlgebra::mult(const ring_elem f, const ring_elem g)
// {
//   // one line function
// }

ring_elem GroebnerAlgebra::mult_by_term(const ring_elem f, // in Groebner algebra
                                        const ring_elem c, // in base field/ring.
                                        const_monomial m) const // a monomial in Groebner algebra.
// Computes c*m*f (m is on the left...!)
{
  //  polyheap result(this);

  // unpack m into an exponent vector: expf[0], ..., expf[nvars_-1]
  exponents_t expf = new int[nvars_];
  M_->to_expvector(m, expf);

  Nterm* result = copy(f);
  ring_elem resultr = result;
  mult_coeff_to(c, resultr);
  result = resultr;
  for (int i=0; i < nvars_; ++i)
    for (int j=0; j < expf[j]; ++j)
      {
        Nterm* thiselem = mult_by_variable(j, result);
        result = thiselem;
      }
  
  // TODO: write this function
  delete [] expf;
  //  return result.value();
  return result;

#if 0
  // What our method might be here: (c is in the base field/ring: say QQ.
  f is a polynomial in normal form
    
  x(j1) x(j2) ... x(jk) f

    need:

    (1) c * xj * f (c = constant, xj = variable, f is a polynomial in normal form).
    (2) xj * (monomial) = xj * (product of variables <= xj) * product of variables > xj)
    (3) xj * (product of variables < xj) * xj^r
    
#endif
}

//////////////////////////////////
// gbvector multiplication ///////
//////////////////////////////////
// These are essentially identical to the two
// routines above.  Perhaps they should be
// formed from a template?
// It seems difficult, since the interfaces are somewhat different.

gbvector *GroebnerAlgebra::gbvector_mult_by_term(
    gbvectorHeap &result,
    const gbvector *f,
    const ring_elem c,  // in the base K_
    const_monomial m,   // monomial, in M_
    int comp) const     // comp is either 0 or a real component.
// Computes c*m*f*e_comp  (where components of f and e_comp add).
{
  //TODO: wrte this function
  return result.value();
}

ring_elem GroebnerAlgebra::power(const ring_elem f, mpz_srcptr n) const
{
  std::pair<bool, int> n1 = RingZZ::get_si(n);
  if (n1.first)
    return power(f, n1.second);
  else
    throw exc::engine_error("exponent too large");
}

ring_elem GroebnerAlgebra::power(const ring_elem f, int n) const
{
  return Ring::power(f, n);
}

// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// indent-tabs-mode: nil
// End:
