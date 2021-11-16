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
#include<poly.h>

using namespace std;



template<typename R>
poly<R> symmetrize(poly<R> p) {
  poly<R> out;
  for(auto it: p) {
    for(permutation p : Sn(NVARS)) {
      out = out.set(p.act_or_fix(it.first), it.second);
    }
  }
  return out;
}

template<typename R>
poly<R> make_elementary_from_exponent(exponent e) {
  poly<R> out(1);
  for(int i = 0; i < NVARS; ++i) {
    out = out * pow(elementary_symmetric<R>(i+1), e[i]);
  }
  return out;
};

template<typename R>
poly<R> make_elementary_from_poly(poly<R> p) {
  poly<R> out;
  for(auto it : p) {
    out = out + it.second * make_elementary_from_exponent<R>(it.first);
  }
  return out;
}


// decompose a given symmetric polynomial into a polynomial of elementary symmetric polynomials.
template<typename R>
poly<R> decompose_elementary(poly<R> p) {
  if (p.zero()) { return poly<R>(); }
  exponent emax = p.lexmax();
  const int cmax = p[emax];

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

  poly killer = cmax * make_elementary_from_exponent<R>(es);
  assert(killer.lexmax() == p.lexmax());
  p = p - killer;
  return cmax * es + decompose_elementary(p);
};

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
      cout << "\t" << p.str() << " | " << xy.str() << " → " << p.act_or_fix(xy).str() << "\n";
    }
  }

  for(int i = 0; i <= NVARS; ++i) {
    set<permutation> si = Sn(i);
    assert(si.size() == factorial(i));
    cout << "Elementary symmetric polynomial on " << i << " vars:" << elementary_symmetric<int>(i).str() << "\n";
  }


  for(int i = 0; i < 100; ++i) {
    poly p = randpoly<int>();
    p = symmetrize(p);
    cout << "symmetric polynomial: " << p.str() << "\n";
    poly out = decompose_elementary(p);
    cout << "\telementary decomposition: " << out.str()  << "\n";
    poly p2 = make_elementary_from_poly(out);
    cout << "\trecovered polynomial: " << p2.str() << "\n";
    assert(p == p2);
  }
