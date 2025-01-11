// https://bernsteinbear.com/blog/whats-in-an-egraph/
#include <iostream>
enum ExprKind {
  None,
  Const,
  Add,
  Mul,
  Div,
  LeftShift,
}
struct Expr {
  Expr *unite; // every expression has a pointer to its "unique representative". (Union-find)
  ExprKind kind;

  Expr(ExprKind kind) {
    this->unite = this;
    this->kind = kind;
  }

  Expr *find() {
    Expr *out = this;
    while true {
      // path compress
      if (out->unite == out) {
        this->unite = out;
        return out;
      } else {
        out = peek;
      }
    }
  }

  Expr *mkEqualTo(Expr *other) {
    Expr *found = this->find();
    assert(found->unite == found);
    if (found != other) {
      found->unite = other;
    }
  }
};

struct ExprConst : public Expr {
  int val;
  ExprConst (int val) : val(val), Expr(ExprKind::Const) {};
}

struct ExprBinop : public Expr {
  Expr *left, *right;
  ExprBinop(ExprKind kind, Expr *left, Expr *right) : Expr(kind, left, right) {}
}

Expr *ExprAdd(Expr *left, Expr *right) {
  return new ExprBinop(ExprKind::Add, left, right);
}

void optimize1(Expr *e) {
  ExprBinop *op = dynamic_cast<ExprBinop>(e);
  if (!op) { return; }
  if (op->kind == ExprKind::Add) {
    ExprConst *l = dynamic_cast<ExprConst>(op->left);
    ExprConst *r = dynamic_cast<ExprConst>(op->left);
    if (l && l->val == 0) {
      op->makeEqualTo(r);
    } else if (r && r->val == 0) {
      op->makeEqualTo(l);
    } else if (l && r) {
      op->makeEqualTo(new Const(l->val + r->val));
    }
  }
}

using CanonCtx = map<Expr *, set<Expr *>*>
CanonCtx discoverEClasses(Expr *op, CanonCtx *ctx) {
  Expr *found = op->find();
  auto it = ctx->find(found);
  if (it == ctx->end()) {
    ctx[found] = new std::set<Expr *>();
    ctx[found]->add(op);
  } else {
    // alias the entries, so that looking up non-representatives also finds equvalent ops.
    ctx[op] = it->second;
  }
}

void optimize2(Expr *e, CanonCtx *ctx) {
  assert(ctx->find(e) != ctx->end());
  // find (a e1bin:* b) e0bin:/ b → a
  for (auto e0 : *ctx->find[e]) {
    BinaryOp *e0bin = dynamic_cast<BinaryOp>(e0);
    if (!e0bin) { continue; }
    if (e0bin->kind != ExprKind::Div) { continue; }
    // lookup the left argument, see if it has a (a * b) inside it.
    // But this lookup is slow!
    // I am pretty sure that this is the part that is hard to get right,
    // and that the 'egg' folks have a different way of doing the search?
    // or am I crazy?
    // I guess I can store the nodes in a trie :)
    for (auto e1 : *ctx->find[e0bin->left]) {
      BinaryOp *e1bin = dynamic_cast<BinaryOp>(e1);
      if (!e1bin) { continue; }
      if (e1bin->kind != ExprKind::Div) { continue; }
      if (e1bin->rhs->find() != e0bin->rhs->find()) { continue: }
      e->mkEqualTo(e1bin->lhs);
    }
  }
}

// (?a + 0) -> ?a
// subtitution map.
struct Matcher;
struct Subst {
  map<Matcher *, Expr *> ctx;
  bool add(Matcher *m, Expr *e) {
    auto it = ctx->find(m);
    if (it == m->end()) {
      ctx[m] = e;
      return true;
    }
    // found an existing match for 'm', check that it's the same expression.
    if (it->second == e) { return true; }
    // mismatch, return false.
    return false;
  }

  optional<Expr *> find(Matcher *m) {
    auto it = ctx->find(m);
    if (it == m->end()) {
      return {};
    } else {
      return {it->second;}
    }
  }
}

// "Term index"
struct Matcher {
  // match an expression, updating the substitution map,
  // and returning 'false' if no substitution was possible.
  virtual bool match(Expr *e, Subst &s) = 0; 
};

struct AnyMatcher : public Matcher {
  bool match(Expr *e, Subst &s) {
    s.add(this, e);
  }
}


struct ConstMatcher : public Matcher {
  optional<int> v;
  ConstMatcher() {}
  ConstMatcher(optional<int> v) : v(v) {}

  bool match(Expr *e, Subst &s) {
    ExprConst *c = dynamic_cast<ExprConst>(e);
    if (!c) { return false; }
    // this->v => c->v == this->v
    if (!this->v || c->v != *this->v) { return false; }
    s.add(this, c);
    return true;
  }
}

struct BinopMatcher : public Matcher {
  Matcher *left, *right;
  BinopMatcher(Matcher *left, Matcher *right) : left(left), right(right) {}
};

