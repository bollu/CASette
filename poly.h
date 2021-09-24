#pragma once
#include <iostream>
#include <map>
#include <assert.h>
#include <utility>
#include <optional>
#include <vector>
#include <algorithm>
#include <set>

using namespace std; 
static const int NVARS = 2; // number of variables X_i
static const int MAX_DEGREE = 30; // total maximum degree of any exponent.
const char NAMES[NVARS+1] = "pq";
                                  

int factorial(int n) {
  if (n <= 1) { return 1; }
  return n * factorial(n-1);
}

struct exponent {
private:
  int es[NVARS]; // exponents.

public:
  exponent() {
    for(int i = 0; i < NVARS; ++i) { es[i] = 0; }
  }

  exponent(const exponent &other) {
    for(int i = 0; i < NVARS; ++i) { es[i] = other.es[i]; }
  }

  exponent(int var, int exp) {
    for(int i = 0; i < NVARS; ++i) { es[i] = 0; }
    assert(var < NVARS); 
    assert(exp >= 0);
    es[var] = exp;
  }

  exponent(map<int, int> exps) {
    for(int i = 0; i < NVARS; ++i) { es[i] = 0; }
    for(auto it: exps) {
      assert(it.first < NVARS);
      assert(it.second >= 0); 
      es[it.first] = it.second;

    }
  }

  int degree() const {
    int tot = 0;
    for(int i = 0; i < NVARS; ++i) {
      tot += es[i];
    }
    return tot;
  }

  int operator [](int i) const {
    assert(i < NVARS);
    return es[i];
  }

  exponent operator +(const exponent &other) const {
    exponent out;
    for(int i = 0; i < NVARS; ++i) {
      out.es[i] = this->es[i] + other.es[i];
    }
    assert(degree() <= MAX_DEGREE);
    return out;
  }

  //try to subtract an exponent from this one, and only return an exponent if the result is legal.
  optional<exponent> operator -(const exponent &other) const {
    exponent out;
    for(int i = 0; i < NVARS; ++i) {
      out.es[i] = this->es[i] - other.es[i];
      if (out.es[i] < 0) { return {}; };
    }
    assert(degree() <= MAX_DEGREE);
    return out;
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
  out +=  "[";
  for(int i = 0; i < NVARS; ++i) {
    if (es[i] == 0) { continue; }
    if (!first) { out += " ";  }
    out += NAMES[i];
    out += "^";
    out += std::to_string(es[i]);
    first = false; 
  }
  out += "]";
  return out;
}

};



struct permutation {
  // private:
  int ps[NVARS]; // [0, 1, 2, .. NVARS-1]
  const int n;


public:
  permutation(int n) : n(n) {
    assert(n >= 0);
    assert(n <= NVARS); 
  }

  permutation(const permutation &other) : n(other.n) {
    for(int i = 0; i < NVARS; ++i) { ps[i] = other.ps[i]; }
  }

  permutation inverse() {
    permutation out(n);
    for(int i = 0; i < n; ++i) {
      out.ps[ps[i]] = i;
    }
    return out;
  }

  // check that the permutation is well formed.
  bool well_formed() const {
    for(int i = 0; i < n; ++i) {
      if (!(ps[i] >= 0 && ps[i] <= NVARS-1)) { return false; }
      for(int j = i + 1; j < n; ++j) {
        if (ps[i] == ps[j]) { return false; }
      }
    }
    return true;

  }

  int act(int i) const {
    assert(i >= 0); assert(i < n);
    return ps[i];
  }

  int act_or_fix(int i) const {
    if (i < 0 || i >= n) { return i; }
    return act(i);
  }

  exponent act(exponent e) const {
    exponent out;
    for(int i = 0; i < NVARS; ++i) {
      out = out.set(act(i), e[i]);
    }
    return out;
  }

  exponent act_or_fix(exponent e) const {
    exponent out;
    for(int i = 0; i < NVARS; ++i) {
      out = out.set(act_or_fix(i), e[i]);
    }
    return out;
  }

string str () const {
  string out;
  out += "[S";
  out += std::to_string(n);
  for(int i = 0; i < n; ++i) {
    if (i == act(i)) { continue; };
    out += ";"; out += std::to_string(i+1); out += "→"; out += std::to_string(act(i)+1);
  }
  out += "]";
  return out;
}


};

bool operator < (const permutation &p, const permutation &q) {
  if (p.n != q.n) {
    return p.n < q.n;
  }
  assert(p.n == q.n);

  for(int i = 0; i < p.n; ++i) {
    if (p.act(i) == q.act(i)) { continue; }
    return p.act(i) < q.act(i);
  }
  return false;
}

set<permutation> Sn(int n) {
  assert(n >= 0);
  assert(n <= NVARS);
  if (n == 0) { 
    permutation p(n); return {p};
  } 
  if (n == 1) { 
    permutation p(n); p.ps[0] = 0; return {p};
  } 
  // else:
  assert(n > 1);
  set<permutation> qs = Sn(n-1);
  set<permutation> out;
  for(permutation q: qs) {
    // insert an [n-1] in all position of the q.
    for(int i = 0; i < n; ++i) {
      permutation p(n);
      for(int j = 0; j < i; ++j) { p.ps[j] = q.ps[j];  }
      p.ps[i] = n-1;
      for(int j = i + 1; j < n; ++j) {
        p.ps[j] = q.ps[j-1];
      }
      out.insert(p);
    }
  }
  return out;
}

// lex ordering.
bool operator < (const exponent &e, const exponent &f) {
  if (e.degree() != f.degree()) { return e.degree() < f.degree(); }
  for(int i = 0; i < NVARS; ++i) {
    if (e[i] == f[i]) { continue; }
    assert(e[i] != f[i]);
    return e[i] < f[i];
  }
  return false;
}

bool operator == (const exponent &e, const exponent &f) {
  for(int i = 0; i < NVARS; ++i) {
    if (e[i] != f[i]) { return false; }
  }
  return true;
}

struct monomial {
  const int coeff;
  const exponent exp;

  monomial(int coeff, exponent exp) : coeff(coeff), exp(exp) {};

  string str() const {
    if (coeff == 0) { return "0"; }
    else {
      return std::to_string(coeff) + exp.str();
    }
  }
};

struct poly {
  // create monomial
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

  poly(int c, exponent e) {
    if (c != 0) {
      coeffs[e] = c;
    }
  }
  poly set(exponent e, int v) const {
    poly out = *this;
    if (v == 0) {
      out.coeffs.erase(e);
    } else {
      out.coeffs[e] = v;
    }
    return out;
  }

  poly incr(exponent e, int deltav) const {
    return set(e, get(e) + deltav);
  }

  exponent lexmax() const {
    auto it = coeffs.rbegin();
    if (it == coeffs.rend()) { return exponent(); }
    else { return {it->first}; }
  };

  monomial leading_term() {
    exponent largest = lexmax();
    return monomial(this->get(largest), largest);
  }

  // return true if p is the zero polynomial
  bool zero() const {
    return coeffs.size() == 0;
  };

  int get(exponent e) const {
    auto it = coeffs.find(e);
    if (it == coeffs.end()) { return 0; }
    return it->second;
  }


  int operator [](exponent e) const {
    return get(e);
  }

  
  using coeffsT = map<exponent, int>;
  using const_iterator = coeffsT::const_iterator;

  const_iterator begin() const { return coeffs.begin(); }
  const_iterator end() const { return coeffs.end(); }

string str () const {
  string out;
  bool first = true;
  if (zero()) { return "0"; }
  for(auto it : this->coeffs) {
    assert(it.second != 0);
    if (!first) { 
      out += ((it.second > 0) ? " + " : " - ");
    } 
    out += std::to_string(abs(it.second)); out += it.first.str();
    first = false;
  }
  return out;
}

  private:
  coeffsT coeffs;
};

// operator (poly)(const monomial &m) {
// }



// find lexicographic max term

poly operator +(const poly&p, const poly &q) {
  poly out = p;
  for(auto it : q) {
    out = out.incr(it.first, it.second);
  }
  return out;
};

poly operator -(const poly&p) {
  poly out;
  for(auto it : p) {
    out = out.set(it.first, -it.second);
  }
  return out;
};


poly operator -(const poly&p, const poly &q) {
  poly out = p;
  for(auto it : q) {
    out = out.incr(it.first, -it.second);
  }
  return out;
};

bool operator == (const poly &p, const poly &q) {
  return (p - q).zero();
}


poly operator *(int c, const exponent &e) {
  return poly(c, e);
}

poly operator *(int c, const poly &p) {
  poly out;
  for(auto it : p) {
      out = out.set(it.first, c * it.second);
  }
  return out;
};

poly operator *(const poly &p, const poly &q) {
  poly out;
  for(auto it1 : p) {
    for(auto it2 : q) {
      out = out.incr(it1.first + it2.first, it1.second * it2.second);
    }
  }
  return out;
};



poly pow(const poly &p, int i) {
  if (i == 0) { return poly(1); };
  if (i == 1) { return p; }
  poly half = pow(p, i/2);
  if (i % 2 == 0) {
    return half * half;
  } else {
    return half * half * p;
  }
}


// create S_1, S_2, S_3, S_4, S_5
poly elementary_symmetric(int n) {
  assert(n >= 0);
  assert(n <= NVARS);
  exponent monomial;
  for(int i = 0; i < n; ++i) { monomial = monomial.set(i, 1); }
  poly out;
  // this is wasteful. Can enumerate this much better.
  for(permutation s : Sn(NVARS)) {
    out = out.set(s.act_or_fix(monomial), 1);
  }
  return out;

};


exponent randexponent() {
  exponent out;
  for(int i = 0; i < NVARS; ++i) {
    if (rand() % 2) {
      out = out.set(i, rand() % 5);
    }
  }
  return out;
}

poly randpoly() {
  int nterms = 1 + rand() % 3;
  poly out;
  for(int i = 0; i < nterms; ++i) {
    int coeff = (1 + (rand() % 4)) * (rand() % 2 ? 1 : -1);
    out = out + coeff * randexponent(); 
  }
  return out;
};
