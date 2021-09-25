// multivariate division from cox little oshea
#include <assert.h>

#include <algorithm>
#include <iostream>
#include <map>
#include <optional>
#include <set>
#include <utility>
#include <vector>
using namespace std;
static const int NVARS = 2;        // number of variables X_i
static const int MAX_DEGREE = 30;  // total maximum degree of any exponent.
const char NAMES[NVARS + 1] = "pq";

int gcd_rec(int small, int large) {
  if (large < small) {
    return gcd_rec(large, small);
  } else {
    if (small == 0) {
      return large;
    } else {
      return gcd_rec(large % small, small);
    }
  }
}

int gcd(int a, int b) { return gcd_rec(abs(a), abs(b)); }

struct QQ {
  int p, q;
  QQ() : p(0), q(1) {}
  QQ(int n) : p(n), q(1) {}
  QQ(int p0, int q0) : p(init_p(p0, q0)), q(init_q(p0, q0)) {}
  QQ(const QQ &other) : p(other.p), q(other.q) {}

  string str() const {
    if (q == 1) {
      return to_string(p);
    }
    return to_string(p) + "/" + to_string(q);
  }

  QQ operator-() const { return QQ(-p, q); }

  bool operator==(const QQ &other) const {
    return p == other.p && q == other.q;
  }

  // a/b < c/d <=> ad < bc
  bool operator<(const QQ &other) { return p * other.q < q * other.p; }

  bool operator>(const QQ &other) { return p * other.q > q * other.p; }

  bool operator !=(const QQ &other) const { return p != other.p || q != other.q; }
  QQ operator+(const QQ &other) const {
    return QQ(p * other.q + q * other.p, q * other.q);
  }

  QQ operator-(const QQ &other) const {
    return QQ(p * other.q - q * other.p, q * other.q);
  }

  QQ operator*(const QQ &other) const { return QQ(p * other.p, q * other.q); }

  QQ operator/(const QQ &other) const { return QQ(p * other.q, q * other.p); }

  QQ recip() const { return QQ(q, p); }

  private:
   static int init_p(int p0, int q0) {
     assert(q0 != 0);
     return p0 / gcd(p0, q0);
   }

   static int init_q(int p0, int q0) {
     assert(q0 != 0);
     return q0 / gcd(p0, q0);
   }
};

std::string to_string(const QQ &q) { return q.str(); }

QQ abs(QQ q) { return QQ(abs(q.p), abs(q.q)); }

using R = QQ;

struct exponent {
 private:
  int es[NVARS];  // exponents.

 public:
  exponent() {
    for (int i = 0; i < NVARS; ++i) {
      es[i] = 0;
    }
  }

  exponent(const exponent &other) {
    for (int i = 0; i < NVARS; ++i) {
      es[i] = other.es[i];
    }
  }

  exponent(int var, int exp) {
    for (int i = 0; i < NVARS; ++i) {
      es[i] = 0;
    }
    assert(var < NVARS);
    assert(exp >= 0);
    es[var] = exp;
  }

  exponent(map<int, int> exps) {
    for (int i = 0; i < NVARS; ++i) {
      es[i] = 0;
    }
    for (auto it : exps) {
      assert(it.first < NVARS);
      assert(it.second >= 0);
      es[it.first] = it.second;
    }
  }

  int degree() const {
    int tot = 0;
    for (int i = 0; i < NVARS; ++i) {
      tot += es[i];
    }
    return tot;
  }

  int operator[](int i) const {
    assert(i < NVARS);
    return es[i];
  }

  exponent operator+(const exponent &other) const {
    exponent out;
    for (int i = 0; i < NVARS; ++i) {
      out.es[i] = this->es[i] + other.es[i];
    }
    assert(degree() <= MAX_DEGREE);
    return out;
  }

  // try to subtract an exponent from this one, and only return an exponent if
  // the result is legal.
  exponent operator-(const exponent &other) const {
    assert(other.divides(*this));

    exponent out;
    for (int i = 0; i < NVARS; ++i) {
      out.es[i] = this->es[i] - other.es[i];
      assert(out.es[i] >= 0);
    }
    assert(degree() <= MAX_DEGREE);
    return out;
  }

  // check if this divides the other
  bool divides(const exponent &other) const {
    for (int i = 0; i < NVARS; ++i) {
      if (other.es[i] - this->es[i] < 0) {
        return false;
      }
    }
    return true;
  }

  exponent set(int i, int val) const {
    assert(i < NVARS);
    assert(val >= 0);
    exponent out = *this;
    out.es[i] = val;
    assert(degree() <= MAX_DEGREE);
    return out;
  }

  string str() const {
    bool first = true;
    string out;
    out += "[";
    for (int i = 0; i < NVARS; ++i) {
      if (es[i] == 0) {
        continue;
      }
      if (!first) {
        out += " ";
      }
      out += NAMES[i];
      out += "^";
      out += std::to_string(es[i]);
      first = false;
    }
    out += "]";
    return out;
  }
};

bool operator<(const exponent &e, const exponent &f) {
  if (e.degree() != f.degree()) {
    return e.degree() < f.degree();
  }
  for (int i = 0; i < NVARS; ++i) {
    if (e[i] == f[i]) {
      continue;
    }
    assert(e[i] != f[i]);
    return e[i] < f[i];
  }
  return false;
}

bool operator==(const exponent &e, const exponent &f) {
  for (int i = 0; i < NVARS; ++i) {
    if (e[i] != f[i]) {
      return false;
    }
  }
  return true;
}

struct monomial {
  const R coeff;
  const exponent exp;

  monomial(R coeff, exponent exp) : coeff(coeff), exp(exp){};

  string str() const {
    if (coeff == 0) {
      return "0";
    } else {
      return to_string(coeff) + exp.str();
    }
  }

  monomial operator*(const monomial &other) const {
    return monomial(this->coeff * other.coeff, this->exp + other.exp);
  }

  // better be sure this division is legal!
  monomial operator/(const monomial &other) const {
    exponent out_exp = this->exp - other.exp;
    return monomial(this->coeff / other.coeff, out_exp);
  }
};

struct poly {
  poly() {}

  poly(const poly &other) : coeffs(other.coeffs) {}

  poly(int c) {
    if (c != 0) {
      coeffs[exponent()] = c;
    }
  }

  poly(monomial m) {
    if (m.coeff != 0) {
      coeffs[m.exp] = m.coeff;
    }
  }

  poly(R c, exponent e) {
    if (c != 0) {
      coeffs[e] = c;
    }
  }
  poly set(exponent e, R v) const {
    poly out = *this;
    if (v == 0) {
      out.coeffs.erase(e);
    } else {
      out.coeffs[e] = v;
    }
    return out;
  }

  poly incr(exponent e, R deltav) const { return set(e, coeff(e) + deltav); }

  exponent lexmax() const {
    auto it = coeffs.rbegin();
    if (it == coeffs.rend()) {
      return exponent();
    } else {
      return {it->first};
    }
  };

  monomial leading_term() {
    exponent largest = lexmax();
    return monomial(this->coeff(largest), largest);
  }

  // return true if p is the zero polynomial
  bool zero() const { return coeffs.size() == 0; };

  R coeff(exponent e) const {
    auto it = coeffs.find(e);
    if (it == coeffs.end()) {
      return 0;
    }
    return it->second;
  }

  R operator[](exponent e) const { return coeff(e); }

  using coeffsT = map<exponent, R>;

  struct const_iterator {
   public:
    operator monomial() { return monomial(it->second, it->first); }
    const_iterator(coeffsT::const_iterator it) : it(it) {}
    void operator++() { ++it; };
    void operator++(int i) { it++; };
    bool operator==(const_iterator &other) const { return it == other.it; }
    bool operator!=(const_iterator &other) const { return it != other.it; }

    monomial operator*() const {
      return monomial(this->it->second, this->it->first);
    }

   private:
    coeffsT::const_iterator it;
  };

  const_iterator begin() const { return coeffs.begin(); }
  const_iterator end() const { return coeffs.end(); }

  string str() const {
    string out;
    bool first = true;
    if (zero()) {
      return "0";
    }
    for (auto it : this->coeffs) {
      assert(it.second != 0);
      if (!first) {
        out += ((it.second > R(0)) ? " + " : " - ");
      }
      out += to_string(abs(it.second));
      out += it.first.str();
      first = false;
    }
    return out;
  }

 private:
  coeffsT coeffs;
};

// find lexicographic max term

poly operator+(const poly &p, const poly &q) {
  poly out = p;
  for (auto it : q) {
    out = out.incr(it.exp, it.coeff);
  }
  return out;
};

poly operator-(const poly &p) {
  poly out;
  for (auto it : p) {
    out = out.set(it.exp, -it.coeff);
  }
  return out;
};

poly operator-(const poly &p, const poly &q) {
  poly out = p;
  for (auto it : q) {
    out = out.incr(it.exp, -it.coeff);
  }
  return out;
};

bool operator==(const poly &p, const poly &q) { return (p - q).zero(); }

poly operator*(R c, const exponent &e) { return poly(c, e); }

poly operator*(R c, const poly &p) {
  poly out;
  for (auto it : p) {
    out = out.set(it.exp, c * it.coeff);
  }
  return out;
};

poly operator*(const poly &p, const poly &q) {
  poly out;
  for (auto it1 : p) {
    for (auto it2 : q) {
      out = out.incr(it1.exp + it2.exp, it1.coeff * it2.coeff);
    }
  }
  return out;
};

poly pow(const poly &p, int i) {
  if (i == 0) {
    return poly(1);
  };
  if (i == 1) {
    return p;
  }
  poly half = pow(p, i / 2);
  if (i % 2 == 0) {
    return half * half;
  } else {
    return half * half * p;
  }
}

exponent randexponent() {
  exponent out;
  for (int i = 0; i < NVARS; ++i) {
    if (rand() % 2) {
      out = out.set(i, rand() % 5);
    }
  }
  return out;
}

poly randpoly() {
  int nterms = 1 + rand() % 3;
  poly out;
  for (int i = 0; i < nterms; ++i) {
    int coeff = (1 + (rand() % 4)) * (rand() % 2 ? 1 : -1);
    out = out + R(coeff) * randexponent();
  }
  return out;
};

// return true if exponent e divicdes polynomial p.
bool does_monomial_divide_poly(monomial m, poly p) {
  for (auto it : p) {
    cout << "\t-does " << m.str() << " divide " << it.str() << " ? = " << m.exp.divides(it.exp) << "\n";
    if (!m.exp.divides(it.exp)) {
      return false;
    }
  }
  return true;
}

// return quotient and remainder
// 2.3: a divison algorithm for k[x1, ... xn]
// r = divisoR
pair<vector<poly>, poly> divide(poly p, vector<poly> rs) {
  const poly f = p;
  poly rem;
  vector<poly> qs(rs.size());
  // loop invariant: f = p + qs[i] rs[i] + rem
  while (!p.zero()) {
    bool divisionOccured = false;
    for (int i = 0; i < rs.size(); ++i) {
      if (rs[i].zero()) {
        continue;
      }
      if (does_monomial_divide_poly(rs[i].leading_term(), p)) {
        const poly delta = poly(p.leading_term() / rs[i].leading_term());
        cout << "δ: " << delta.str() << " | rs[i]: " << rs[i].str() << " | p: " << p.str() << "\n";
        getchar();
        qs[i] = qs[i] + delta;
        p = p - delta * rs[i];
        divisionOccured = true;
      }
    }
    // cout << "divide p: " << p.str() << " | division occured? " <<
    // divisionOccured << "\n";

    if (!divisionOccured) {
      rem = rem + poly(p.leading_term());
      p = p - poly(p.leading_term());
    }
  }
  return {qs, rem};
}

int main() {
  srand(42);

  for (int i = 0; i < 100; ++i) {
    poly p = randpoly();
    poly r1 = randpoly();
    poly r2 = randpoly();
    vector<poly> qs;
    poly rem;
    tie(qs, rem) = divide(p, {r1, r2});
    poly check = qs[0] * r1 + qs[1] * r2 + rem;
    // for(auto it : rem) {
    //   assert(!r1.leading_term().divides(it.first));
    // }

    assert(check == p);
    cout << "\n===\ncomputing:";
    cout << "\n\t" << p.str() << " / <" << r1.str() << " |" << r2.str() << ">";
    cout << "\n\t(" << qs[0].str() << ")*(" << r1.str() << ") + ("
         << qs[1].str() << ")*(" << r2.str() << ")"
         << " + " << rem.str() << " = " << check.str() << "\n";
  }
};
