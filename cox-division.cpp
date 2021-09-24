// fundamental theorem of symmetric polynomials: any symmetric polynomial can be written
// as a function of the elementary symmetric polynomial
#include <iostream>
#include <map>
#include <assert.h>
#include <utility>
#include <optional>
#include <vector>
#include <algorithm>
#include <set>
#include <poly.h>

int gcd(int small, int large) {
  if (small > large) { return gcd(large, small); }
  if (small == 0) { return large; }
  return gcd(large % small, small);
}

struct QQ {
  int p, q;
  QQ() : p(0), q(1) {}
  QQ(int n) : p(n), q(1) {}
  QQ(int p0, int q0) : p(p0/gcd(p0, q0)), q(q0/gcd(p0, q0)) {}
  QQ(const QQ&other) : p(other.p), q(other.q) {}

  string str() const {
    if(q == 1) { return to_string(p); }
    return to_string(p) + "/" + to_string(q);
  }

  QQ operator -() const {
    return QQ(-p, q);
  }
  bool operator == (const QQ &other) const {
    return p == other.p && q == other.q;
  }

  bool operator != (const QQ &other) const {
    return !(p == q); 
  }
  QQ operator +(const QQ &other) const {
    return QQ(p * other.q + q * other.p, q * other.q);
  }

  QQ operator - (const QQ &other) const {
    return QQ(p * other.q - q * other.p, q * other.q);
  }

  QQ operator * (const QQ &other) const {
    return QQ(p * other.p, q * other.q);
  }

  QQ operator / (const QQ &other) const {
    return QQ(p * other.q, q * other.p);
  }

  QQ recip() const {
    return QQ(q, p);
  }
};

namespace std {
std::string to_string(const QQ &q) {
  return q.str();
}
}




// return quotient and remainder
// 2.3: a divison algorithm for k[x1, ... xn]
// r = divisoR
template<typename R>
pair<vector<poly<R>>, poly<R>> divide(poly<R> p, vector<poly<R>> rs) {
  const poly f = p;
  poly<R> rem;
  vector<poly<R>> qs(rs.size());
  // loop invariant: f = p + qs[i] rs[i] + rem
  while(!p.zero()) {
    bool divisionOccured = false;
    for(int i = 0; i < rs.size(); ++i) {
      optional<exponent> q = p.leading_term().exp - rs[i].leading_term().exp;
      if (!q) { continue; } 
      else {
        qs[i] = qs[i] + poly(p.leading_term().coeff / rs[i].leading_term().coeff, *q);
        divisionOccured = true;
      }
    }
    
    if (!divisionOccured) {
      rem = rem + poly(p.leading_term());
      p = p - poly(p.leading_term());
    }
  }
  return {qs, rem};
}

int main() {
  srand(42);


  for(int i = 0; i < 100; ++i) {
    poly p = randpoly<QQ>();
    poly r1 = randpoly<QQ>();
    poly r2 = randpoly<QQ>();
    vector<poly<QQ>> qs;
    poly<QQ> rem;
    cout << "computing " << p.str() << " / [" << r1.str() << ", " << r2.str() << "]\n";
    tie(qs, rem) = divide(p, {r1, r2});
  }
};
