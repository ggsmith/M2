// Copyright 2025 The Macaulay2 Authors

#pragma once

#include "poly.hpp"
#include "gbring.hpp"

#include <vector>
///// Ring Hierarchy ///////////////////////////////////

class GroebnerAlgebra : public PolyRing
{
  const Matrix * mC; // scalars showing up in commutation of variables
  const Matrix * mD; // trailing terms showing up in commutation of variables
  std::vector<int> mSquaringIndices;

  void initialize1();
  bool initialize_groebner_algebra(const Matrix* C, const Matrix* D, const std::vector<int>& squaringIndices);
  GroebnerAlgebra() : mC(nullptr), mD(nullptr), mSquaringIndices() {}
  virtual ~GroebnerAlgebra() {}

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
