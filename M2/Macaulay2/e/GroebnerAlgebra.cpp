// Copyright 2025 The Macaulay2 Authors

// TODO made 11 Mar 2026, updated on 3 April 2026.
// DONE 1. populate mMultTable in the constructor of GroebnerAlgebra
// 1a. get squares working
// 1b. clean up the interface, removing the old stuff, or having front end produce the "E" matrix.
// DONE 2. make sure mult_var_var is accessing this table correctly.
// 3. Test it! TODO: write a number of tests, using WeylAlgebra and Associative algebras to try both, use toString, compare.
// 4. GBRing stuff.
// 5. Should we be caching any multiplications?
// 6. how do we do x_i^2? Does it change or not?

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

bool GroebnerAlgebra::initialize_groebner_algebra(const Matrix* E)
{
  // We create the mult table for x_j * x_i.

  this->mE = E;
  int nvars = n_vars();
  mMultTable = new Nterm** [nvars];
  for (int i=0; i<nvars; ++i)
    {
      mMultTable[i] = new Nterm* [nvars];
      for (int j=0; j<nvars; ++j)
        mMultTable[i][j] = nullptr;
    }

  int v = 0;
  int w = 0;
  for (int k = 0; k < E->n_cols(); ++k)
    {
      ring_elem f = E->elem(0, k);
      ring_elem copyf = this->copy(f);
      Nterm* ourf = copyf.poly_val;
      std::cout << "setting " << w << " and " << v << std::endl;
      mMultTable[w][v] = ourf;
      if (w < nvars - 1) ++w;
      else {
        if (v < nvars - 1)
          {
            ++v;
            w = v;
          }
        else
          {
            // we are hopefully done.  Need to give an error if the sizes are wrong.
          }
      }
    }
  return true;
}

GroebnerAlgebra *GroebnerAlgebra::create(const Matrix* E) // of length binomial(n+1,2), over a polynomial ring in n variables.
{
  std::cout << "We are in the c++ constructor" << std::endl;
  const Ring* R = E->get_ring();
  const PolynomialRing *P = R->cast_to_PolynomialRing();
  if (P == nullptr)
    {
      throw exc::engine_error("expected a matrix over a polynomial ring");
    }

  GroebnerAlgebra *result = new GroebnerAlgebra;
  result->initialize_poly_ring(P->getCoefficients(), P->getMonoid());

  //  std::vector<int> squaring { M2_arrayint_to_stdvector<int>(squaring_indices) };
  
  if (!result->initialize_groebner_algebra(E)) return nullptr;

  //TODO: what is this?   result->gb_ring_ = GBRing::create_GroebnerAlgebra(K, M, weyl);
  return result;
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
      result = (var(j)).poly_val; // is this const?
    }
  else if (i <= j) // TODO: with squares, this should be i < j.
    {
      a[j]++;
      ring_elem f = make_logical_term(K_, K_->one(), a);
      result = f.poly_val;
      a[j]--;
    }
  else
    {
      // here j < i // TODO: with squares, here j <= i
      a[i]--;
      const Nterm* f = mult_var_var(i, j);
      result = mult_exp_poly(a, f);
      a[i]++;
    }
  return result;
}

Nterm* GroebnerAlgebra::mult_exp_poly(exponents_t a, const Nterm* f) const
//  x^a * f
// sum of coeff * mult_exp_exp(a, term of f).
{
  polyheap result(this);
  exponents_t exp = new int[nvars_];
  for (const Nterm* s = f; s != nullptr; s = s->next)
    {
      M_->to_expvector(s->monom, exp);
      Nterm* st = mult_exp_exp(a, exp);
      mult_coeff_to_poly(s->coeff, st);
      result.add(st);
    }
  delete [] exp;
  return result.value();
}

Nterm* GroebnerAlgebra::mult_poly_exp(const Nterm* f, exponents_t a) const
//  f * x^a
// sum of coeff * mult_exp_exp(term of f, a).
{
  polyheap result(this);
  exponents_t exp = new int[nvars_];
  for (const Nterm* s = f; s != nullptr; s = s->next)
    {
      M_->to_expvector(s->monom, exp);
      Nterm* st = mult_exp_exp(exp, a);
      mult_coeff_to_poly(s->coeff, st);
      result.add(st);
    }
  delete [] exp;
  return result.value();
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
      ring_elem f = make_logical_term(K_, K_->one(), a);
      return f.poly_val;
    }
  b[i]--;  // now b is b'
  Nterm* f = mult_exp_var(a, i);
  Nterm* result = mult_poly_exp(f, b);
  b[i]++; // changes b' back to b
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
  mult_coeff_to_poly(K_->mult(cf, cg), fg);

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
  exponents_t exp = new int[nvars_];

  M_->to_expvector(m, exp);
  Nterm* result = mult_exp_poly(exp, f.poly_val);
  mult_coeff_to_poly(c, result);

  delete [] exp;
  return result;
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
