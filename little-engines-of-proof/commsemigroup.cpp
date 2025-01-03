#!/usr/bin/env cling

//Decision procedure for equality in commutative semirings.
using namespace std;
#include <iostream>
#include <map>
#include <assert.h>
#include <string>

struct Word {
  map<char, int> nf;
  Word(std::string s) {
    for (int i = 0;i < s.size(); ++i) { nf[s[i]]++; }
  }
  Word(map<char, int> nf) : nf(nf) {}

  int count(char c) const {
    auto it = nf.find(c);
    if (it == nf.end()) { return 0; }
    return it->second;
  }

  // least upper bound of the two rewrites.
  Word lub(const Word &other) const {
    map<char, int> out;
    for (char c = 'a'; c < 'z'; ++c) {
      out[c] = std::max<int>(nf.count(c), this->count(c));
    }
    return Word(out);
  }

  bool operator == (const Word &other) {
    return nf == other.nf;
  }
  
  bool operator < (const Word &other) {
    for (char c = 'a'; c <= 'z'; ++c) {
      if (this->count(c) > other.count(c)) {
        return true;
      }
    }
    return false;
  }
};

ostream &operator << (ostream &o, const Word &w) {
  o << "<";
  for (char c = 'a'; c <= 'z'; ++c) {
    for(int i = 0; i < w.count(c); ++i) {
      o << c;
    }
  }
  o << ">";
  return o;
}

struct Equality {
  Word lhs, rhs;
  Equality(Word lhs, Word rhs) : lhs(lhs), rhs(rhs) {};
};

struct RewriteRule {
  Word lhs, rhs;

  RewriteRule(Word lhs, Word rhs) : lhs(lhs), rhs(rhs) {
    assert(rhs < lhs); // oriented rule.
  }

  optional<Word> apply(const Word w) const {
    Word out = w;
    for (char c = 'a'; c <= 'z'; ++c) {
      out.nf[c] -= lhs.count(c);
      // we are unable to apply the rewrite, so bail out.
      if (out.nf[c] < 0) { return {}; }
      // we assume we can apply the rewrite, so we update the count of 'c'.
      out.nf[c] += rhs.count(c);
    }
    return out;
  }
};

// orient an equality to produce a rewrite rule.
// Will produce no rewrite rule if lhs and rhs are identical.
std::optional<RewriteRule> mkRewriteRuleFromEquality(Equality eq) {
  if (eq.lhs == eq.rhs) {
    return {};
  } else if (eq.lhs < eq.rhs) {
    return RewriteRule(eq.rhs, eq.lhs);
  } else {
    return RewriteRule(eq.lhs, eq.lhs);
  }
}

// the two words will cause their lub to be rewritten
// non-confluently if they have nontrivial symmetric difference.
bool isCriticalPair(const Word &a, const Word &b) {
  bool shared = false;
  bool unshared = false;
  for (char c = 'a'; c <= 'z'; ++ c) {
    shared = shared || (a.count(c) > 0 && b.count(c) > 0);
    unshared = unshared || (a.count(c) > 0 && b.count(c) == 0) || (a.count(c) == 0 && b.count(c) > 0);
  }
  return shared && unshared;
}
// a -> b
// p -> q
//
//  lub(a, p)
//   /     \
// b' =eq=  q'
//
// To impose confluence, we add the rewrite (b' = q'), which will then be oriented into a rewrite
// for the rewrite system.
Equality mkRewritesConfluent(RewriteRule r, RewriteRule s) {
  Word w = r.lhs.lub(s.lhs); // compute lub
  Word rout = *r.apply(w);
  Word sout = *s.apply(w);
  return Equality(rout, sout);
}

struct CommSemigroupSolver {
  // efficient way to do this?
  vector<RewriteRule> rewrites;

  void addCriticalPairs() {
    while(true) {
      vector<RewriteRule> newRewrites;
      for (RewriteRule &r : rewrites) {
        for (RewriteRule &s : rewrites) {
          if (!isCriticalPair(r.lhs, s.lhs))  { continue; }
          std::optional<RewriteRule> confluencer = mkRewriteRuleFromEquality(mkRewritesConfluent(r, s));
          if (!confluencer) { continue; }
          newRewrites.push_back(*confluencer);
        }
      }
      if (!newRewrites.size()) { return; }
      std::copy(newRewrites.begin(), newRewrites.end(), rewrites.end());
    }
  }

  void addRewrite(RewriteRule r) {
    rewrites.push_back(r);
    addCriticalPairs();
  }

  Word normalForm(Word w) {
    bool changed = true;
    while(changed) {
      changed = false;
      for (RewriteRule &r : rewrites) {
        optional<Word> x = r.apply(w);
        if (!x) { continue; }
        assert(*x < w);
        w = *x;
        changed = true;
      }
    }
    return w;
  }
};

int commsemigroup() {
  std::cout << "XX";
  return 42;
}

int main() {
  std::cout << "XX";
  return 0;
}
