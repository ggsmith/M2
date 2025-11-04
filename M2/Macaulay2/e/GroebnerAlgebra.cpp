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

ring_elem GroebnerAlgebra::mult_by_term(const ring_elem f,
                                    const ring_elem c,
                                    const_monomial m) const
// Computes c*m*f
{
  polyheap result(this);

  // TODO: write this function
  return result.value();
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
