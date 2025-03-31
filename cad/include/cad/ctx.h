// Cylindrical Algebraic Decomposition in Macaulay2
//   + https://arxiv.org/pdf/2503.21731v1
// Programming and certifying the CAD algorithm inside the Coq system:
//  + https://drops.dagstuhl.de/storage/16dagstuhl-seminar-proceedings/dsp-vol05021/DagSemProc.05021.17/DagSemProc.05021.17.pdf
// How to use CAD:
//   + https://www.emis.de/journals/SLC/wpapers/s65kauers.pdf
#include <string>
#include "flint/fmpz_mpoly.h"
#include "flint/fmpz_mpoly_factor.h"
#include "arb/acb_poly.h"

namespace cad  {

struct Context;
struct Poly;

struct Context {
  private:
  flint_rand_t m_state;
  fmpz_mpoly_ctx_t m_ctx;
  int m_nvars;

  public:
  Context(int nvars);

  friend struct Poly;
};

struct Poly {
  Poly(Context& ctx, std::string pretty_val="");
  ~Poly() { fmpz_mpoly_clear(m_poly); }
  // fmpz_mpoly_resultant(res, f, g, 0, ctx);
private:
  Context &m_ctx;
  fmpz_mpoly_t m_poly;

};

std::string operator << (std::ostream &o, const Poly &p);

struct UniPolyRoot {
  acb_t m_root;
  UniPolyRoot (acb_t root) : m_root(root) {};
};

std::string operator << (std::ostream &o, const UniPolyRoot &root);

struct UniPolyRoots {
  acb_poly_t m_arb_poly;
  vector<UniPolyRoot> m_roots;
};

// univariate polynomial.
struct UniPoly {
  UniPoly(Context& ctx, std::string pretty_val="");
  ~UniPoly() { fmpz_poly_clear(m_poly); }

  UniPolyRoots roots(int poly_precision, int root_precision);
private:
  Context &m_ctx;
  fmpz_poly_t m_poly;
};

std::string operator << (std::ostream &o, const UniPoly &p);

} // end cad.
