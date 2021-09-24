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

using namespace std;

static const int NVARS = 2; // number of variables X_i
static const int MAX_DEGREE = 30; // total maximum degree of any exponent.
// const char NAMES[NVARS+1] = "pqrst";
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
    assert(var < NVARS); 
    assert(exp >= 0);
    es[var] = exp;
  }

  exponent(map<int, int> exps) {
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

  exponent set(int i, int val) const {
    assert(i < NVARS);
    assert(val >= 0);
    exponent out = *this;
    out.es[i] = val;
    assert(degree() <= MAX_DEGREE);
    return out;
  }
};


ostream &operator << (ostream &o, const exponent &e) {
  bool first = true;
  o << "[";
  for(int i = 0; i < NVARS; ++i) {
    if (e[i] == 0) { continue; }
    if (!first) { o << " ";  }
    o << NAMES[i] << "^" << e[i];
    first = false; 
  }
  o << "]";
  return o;
}


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

struct poly {
  // create monomial
  poly() {}

  poly(const poly &other) : coeffs(other.coeffs) {}

  poly(int c) { 
    if (c != 0) {
      coeffs[exponent()] = c;
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
  private:
  coeffsT coeffs;
};


ostream &operator << (ostream &o, const permutation &p) {
  o << "[S" << p.n;
  for(int i = 0; i < p.n; ++i) {
    if (i == p.act(i)) { continue; };
    o << ";" << i+1 << "→" << p.act(i)+1;
  }
  return o << "]";
}

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

ostream &operator << (ostream &o, const poly &p) {
  bool first = true;
  if (p.zero()) { o << "0"; return o; }
  for(auto it : p) {
    assert(it.second != 0);
    if (!first) { 
      o << ((it.second > 0) ? " + " : " - ");
      o << abs(it.second) << it.first;
    } else {
      o << it.second << it.first;
      first = false;
    }
  }
  return o;
}


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

// decompose a given symmetric polynomial into a polynomial of elementary symmetric polynomials.
poly decompose_elementary(poly p) {
  cout << __FUNCTION__ << " p:" << p << "\n";
  if (p.zero()) { return poly(); }
  exponent emax = p.lexmax();
  const int cmax = p[emax];
  cout << __FUNCTION__ << " emax: " << emax << " | cmax:" << cmax << "\n";

  exponent es; // we use the elementary symmetric polynomails σ[i]^(emax[i] - emax[i-1])
  // x^a y^b = (x)^p (xy)^q
  // [a b] = p [1, 0] + q [1, 1]
  // p = a
  // p + q = b
  // subject to p, q >= 0
  // choose q = b, p = a - b
  int prev = 0;
  for(int i = NVARS-1; i >= 0; i--) {
    es = es.set(i, emax[i] - prev); prev = emax[i];
  }
  cout << __FUNCTION__ << " es: " << es << "\n"; 

  poly killer(1);
  for(int i = 0; i < NVARS; ++i) {
    const poly scale = pow(elementary_symmetric(i+1), es[i]);
    cout << "\t-" << killer << " * " << scale << " = " << killer * scale << "\n";
    killer = killer * scale;
  }
  killer = cmax * killer;
  cout << __FUNCTION__ << " killer: " << killer << "\n";
  getchar();
  assert(killer.lexmax() == p.lexmax());
  p = p - killer;
  return killer + decompose_elementary(p);
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


poly symmetrize(poly p) {
  poly out;
  for(auto it: p) {
    for(permutation p : Sn(NVARS)) {
      out = out.set(p.act_or_fix(it.first), it.second);
    }
  }
  return out;
}

int main() {
  srand(42);

  map<exponent, int> foo;
  foo[exponent(1, 3)] = 16;
  foo[exponent(1, 3)] = -16;
  assert(foo.size() == 1);

  for(int i = 0; i <= NVARS; ++i) {
    set<permutation> si = Sn(i);
    assert(si.size() == factorial(i));
    cout << "size of Sn(n=" << i << ") = " << si.size() << "\n";
    for(permutation p : si) {
      exponent xy({{0, 1}, {1, 1}});
      cout << "\t" << p << " | " << xy << " → " << p.act_or_fix(xy) << "\n";
    }
  }

  for(int i = 0; i <= NVARS; ++i) {
    set<permutation> si = Sn(i);
    assert(si.size() == factorial(i));
    cout << "Elementary symmetric polynomial on " << i << " vars:" << elementary_symmetric(i) << "\n";
  }


  for(int i = 0; i < 100; ++i) {
    poly p = randpoly();
    p = symmetrize(p);
    cout << "symmetric polynomial: " << p << "\n";
    poly out = decompose_elementary(p);
    cout << "\n\telementary decomposition:" << out  << "\n";
  }

};
