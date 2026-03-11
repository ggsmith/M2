// Copyright 2025 The Macaulay2 Authors

// TODO(11 Feb 2026, for next week)
// Implement the non-commutative Groebner algebra multiplication.
// f = c1 x^a1 + c2 x^a2 + ... + cr x^ar // polynomial in the Groebner algebra.
// compute c * x^b * f // c is in the base ring/field, x^b is a monomial in normal form/
// compute c * ci * x^b * x^ai as a polynomial in normal form.
// add all the results together.

// computing x^b * x^a.
// x^b1 * x_i * x_j * x^a1
//   i < j: result is just the monomial.
//   i > j: x^b1 * (cji * x_j * x_i + dji) * x^a1
//      = cji * x^b1 * x_j * x_i * x^a1  +  x^b1 * dji * x^a1
//      = cji * mult(x^b1, x_j) * mult(x_i, x^a1)

// need: mult(x^a, x_i), mult(x_i, x^a)
// these return full polynomials.
// 
// f = m1 + m2 + ..., g = n1 + n2 + ..., sums of monomials
// f*g
// f*n, or m*g
// m*n (m, n are in order, given by exponent vectors)
// m * xi^ei, returns a polynomial
// m * xi
// xj^aj * xi^ai

#pragma once

#include "poly.hpp"
#include "gbring.hpp"

#include <vector>
///// Ring Hierarchy ///////////////////////////////////

class GroebnerAlgebra : public PolyRing
{
  const Matrix * mC; // scalars showing up in commutation of variables
  const Matrix * mD; // trailing terms showing up in commutation of variables
  Nterm*** mMultTable;
  std::vector<int> mSquaringIndices;

  void initialize1();
  bool initialize_groebner_algebra(const Matrix* C, const Matrix* D, const std::vector<int>& squaringIndices);
  GroebnerAlgebra() : mC(nullptr), mD(nullptr), mSquaringIndices() {}
  virtual ~GroebnerAlgebra() {}

private:  
  Nterm* mult_by_variable(int v, Nterm* f) const;
  
  const Nterm* mult_var_var(int v, int w) const;
  Nterm* mult_exp_var(exponents_t a, int w) const;
  Nterm* mult_exp_poly(exponents_t a, const Nterm* ft) const;
  Nterm* mult_poly_exp(const Nterm* ft, exponents_t a) const;
  Nterm* mult_exp_exp(exponents_t a, exponents_t b) const;
  Nterm* mult_term_term(const Nterm* ft, const Nterm* gt) const;
  Nterm* mult_poly_poly(const Nterm* f, const Nterm* g) const;

 public:
  static GroebnerAlgebra *create(const Matrix* C,
                                 const Matrix* D,
                                 M2_arrayint squaring_indices);

  virtual bool is_commutative_ring() const { return false; }
  virtual bool is_groebner_algebra() const { return true; }
  virtual const GroebnerAlgebra *cast_to_GroebnerAlgebra() const { return this; }

  virtual void text_out(buffer &o) const;
  virtual ring_elem power(const ring_elem f, mpz_srcptr n) const;
  virtual ring_elem power(const ring_elem f, int n) const;

 public:
  virtual ring_elem mult_by_term(const ring_elem f,
                                 const ring_elem c,
                                 const_monomial m) const;

  gbvector *gbvector_mult_by_term(
      gbvectorHeap &result,
      const gbvector *f,
      const ring_elem c,  // in the base K
      const_monomial m,   // monomial, in M
      int comp) const;    // comp is either 0 or a real component.
};

// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// indent-tabs-mode: nil
// End:
