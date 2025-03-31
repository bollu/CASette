#include "cad/ctx.h"
// https://arxiv.org/pdf/2503.21731v1#page=15&zoom=100,113,850

namespace cad {
Context::Context(int nvars) : m_nvars(nvars) {
  flint_rand_init(m_state);
  fmpz_mpoly_ctx_init(m_ctx, m_nvars, ORD_LEX);
}

Poly::Poly(Context& ctx, std::string pretty_val) : m_ctx(ctx) {
  fmpz_mpoly_init(m_poly, ctx.m_ctx);
  if (pretty_val.size()) {
    fmpz_mpoly_set_str_pretty(m_poly, pretty_val.c_str(), NULL, m_ctx.m_ctx);
  }
}

std::string operator << (std::ostream &o, const Poly &p) {
  char *s = fmpz_mpoly_get_str_pretty(p.m_poly, p.m_ctx.m_ctx);
  o << s;
  flint_free(s);
  return o;
}

UniPoly::UniPoly(Context& ctx, std::string pretty_val) : m_ctx(ctx) {
  fmpz_poly_init(m_poly);
  if (pretty_val.size()) {
    fmpz_poly_set_str(m_poly, pretty_val.c_str());
  }
}

std::string operator << (std::ostream &o, const UniPoly &p) {
  char *s = fmpz_poly_get_str(p.m_poly);
  o << s;
  flint_free(s);
  return o;
}

UniPolyRoots UniPoly::roots(int poly_precision, int root_precision) {
  UniPolyRoots roots;
  acb_poly_init(roots.m_arb_poly);
  acb_poly_set_fmpq_poly(roots.m_arb_poly, m_poly, poly_precision); // 64 bits precision
  const int DEGREE = acb_poly_degree(roots.m_arb_poly);
  acb_ptr roots_vec = _acb_vec_init(DEGREE);

  // Find roots with 53 bits target precision
  int n_found_roots = 0;
  acb_poly_find_roots(roots_vec, roots.m_arb_poly, NULL, 0, root_precision, n_found_roots);

  for (slong i = 0; i < found_roots; i++) {
    roots.m_roots.push_back(UniPolyRoot(roots + i));
  }
  return roots;
}

std::string operator << (std::ostream &o, const UniPolyRoot &root) {
  // TODO: allow this to change.
  char* str = acb_get_str(z, 10); // 10 digits
}

} // end cad.


