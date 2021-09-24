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

struct rational {
  const int p, q;
  rational(int n) : p(n), q(1) {}
  rational(int p0, int q0) : p(p0/gcd(p0, q0)), q(q0/gcd(p0, q0)) {}

  string to_str() const {
    if(q == 1) { return to_string(p); }
    return to_string(p) + "/" + to_string(q);
  }

  rational operator +(const rational &other) const {
    return rational(p * other.q + q * other.p, q * other.q);
  }

  rational operator - (const rational &other) const {
    return rational(p * other.q - q * other.p, q * other.q);
  }

  rational operator * (const rational &other) const {
    return rational(p * other.p, q * other.q);
  }

  rational operator / (const rational &other) const {
    return rational(p * other.q, q * other.p);
  }

  rational recip() const {
    return rational(q, p);
  }
};

// return quotient and remainder
// 2.3: a divison algorithm for k[x1, ... xn]
// r = divisoR
pair<vector<poly>, poly> divide(poly p, vector<poly> rs) {
  const poly f = p;
  poly rem;
  vector<poly> qs(rs.size());
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
      rem = rem + p.leading_term();
      p = p - p.leading_term();
    }
  }
  return {qs, rem};
}

int main() {
  srand(42);


  for(int i = 0; i < 100; ++i) {
    poly p = randpoly();
    poly q = randpoly();
  }
};
