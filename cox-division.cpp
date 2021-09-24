// multivariate division from cox little oshea
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
  cout << "gcd " << small << " " << large << endl << "\n";
  if (large < small) { return gcd(small, large); }
  else {
    if (small == 0) { return large; }
    else { return gcd(large % small, small); }
  }
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

std::string to_string(QQ &q) {
  return q.str();
}



// return true if exponent e divicdes polynomial p.
template<typename R>
bool does_monomial_divide_poly(monomial<R> m, poly<R> p) {
  for(auto it : p) {
    optional<exponent> delta = it.first - m.exp;
    if (!delta) { return false; }
    if (it.second % m.coeff != 0) { return 0; }
  }
  return true;
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
      if (rs[i].zero()) { continue; }
      if (does_monomial_divide_poly<R>(rs[i].leading_term(), p)) {
        const poly delta = poly(p.leading_term() / rs[i].leading_term());
        // cout << "δ: " << delta.str() << " | rs[i]: " << rs[i].str() << " | p: " << p.str() << "\n";
        // getchar();
        qs[i] = qs[i] + delta; 
        p = p - delta * rs[i]; 
        divisionOccured = true;
      }
    }
    // cout << "divide p: " << p.str() << " | division occured? " << divisionOccured << "\n";
    
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
    poly p = randpoly<int>();
    poly r1 = randpoly<int>();
    poly r2 = randpoly<int>();
    vector<poly<int>> qs;
    poly<int> rem;
    tie(qs, rem) = divide(p, {r1, r2});
    poly<int> check = qs[0]  * r1 + qs[1] * r2 + rem;
    // for(auto it : rem) {
    //   assert(!r1.leading_term().divides(it.first));
    // }

    assert(check == p);
    cout << "\n===\ncomputing:";
    cout << "\n\t" << p.str() << " / <" << r1.str() << " |" << r2.str() << ">";
    cout << "\n\t(" << qs[0].str() << ")*(" << r1.str() << ") + (" << qs[1].str() << ")*(" << r2.str() <<  ")" << 
        " + " << rem.str() << " = " << check.str() << "\n";
  }
};
