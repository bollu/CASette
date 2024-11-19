// Authors: Siddharth Bhat
// DRAT proof format
// https://github.com/marijnheule/drat-trim


// <proof>       = { <comment> | <clause> | "d" <blank> <clause> }
// <comment>     = "c " <anything> "\n"
// <clause>      = { <blank> }{ <lit> } "0"
// <lit>         = <pos> <blank> | <neg> <blank>
// <pos>         = "1" | "2" | .... | <max-idx>
// <neg>         = "-" <pos>
// <blank>       = " " | "\n" | "\t"

// #### Negation of a clause
// merijn: Let C be a clause. NOT(C) denotes the negation of a clause, which is a conjunction of all negated literals in C.
//
// #### AT property
// merijn: A clause C has the redundancy property Asymmetric Tautology (AT) with respect to a CNF formula F iff
// UCP on F AND NOT(C) results in a conflict.
//
// bollu: We want (F => C) to be a tautology, so we show that `!(F => C)` is UNSAT.
// That is we show that `!(!F || C)` has a resolution proof, which is
// `F && !C` has a resolution proof [i.e. results in a conflict].
// This is the AT property, because we are showing : (F => C (implication is asymmetric) is a tautology)
//
//
// #### RAT property
// merijn: The core redundancy property used in the DRAT format is Resolution Asymmetric Tautology (RAT).
//
// merijn: A clause C has the RAT property with respect to a CNF formula F if there exists a literal l in C such
// that for all clauses D in F with -l in D, the clause C OR (D \ {-l}) has the property AT with respect to F.
// Notice that RAT property is a generalization of the AT property.
//
// merijn: This is a generalization of the pure literal rule, and is also
// called the "blocked clause rule" by merijn in his literature.
//
// bollu
// The key idea is this: We want to add a clause C,
// using the literal `l` as the resolution literal.
// let `l` occur positively in C WLOG.
//
// We know that for all D where -l ∈ D, `|- F => C \/ (D / l)`.
//
// #### Special Case 1: Any clause C, no clause D
// First suppose that for a literal `l`, no such `D` exists.
// Then we can safely use the partial assignment `[l -> T]`, since `l` only occurs positively.
// Thus, it's perfectly safe to add a clause `C`, which is of the form `(l \/ <stuff>)`.
// Then we can safely learn the clause `C`,
//
// #### Special Case 2: Clause C = {l}, one clause D = !l \/ D0
//
// - By the RAT property, we know that for any model `M |= F` we also have that `M |= C \/ D0`, which is `M |= l \/ D0`.
// - We claim that `M' := M[l := T]` satisfies `M' |= F /\ C` iff `M |= F`, so we can safely learn clause `C`.
// - If `M[l] = T`, then we have `M = M'`, and clearly `M' |= C`, and thus we are done.
// - So suppose `M[l] = F`. Now, we know that `M |= l \/ D0`, which implies that `M |= D0` (since `M[l] = F`.)
// - Therefore, we have that `M' |= D0`, since `M'` only modifies `l`, and thus leaves `D0`
// - Thus, we have that `M' |= F`, since no other clause in `M` is made less satisfible by setting `l = T`.
// - We also have that `M' |= l` therefore `M' |= C`.
// - So, we show that `M' |= F /\ C`.
//
//
// #### General case 3: Let `C = l \/ C0`, `D = !l \/ D0`.
//
// - First, see that the condition being that `M |= F` implies `M |= C \/ D` is trivial, because `C \/ D` will contain `l` and `!l`,
//   so we must remove one of these :)
// - So, let's try to repeat the same proof.
// - By the RAT property, we know that for any model `M |= F`, we also have `M |= l \/ C0 \/ D0`.
// - Take a model `M` such that `M |= F`. Suppose `M[l] = T`, then we are immediately done becase `M |= C`.
// - So suppose `M[l] = F`. We know from the RAT property that `M |= l \/ C0 \/ D0` which means `M |= C0 \/ D0`.
// - Suppose we know that `M |= C0`, then we are done, since we can use the same model `M' := M` such that `M |= F` as well as `M |= C`.
// - So suppose that `M |/= C0`. Then we must have that `M |= D0`.
// - I now set `M' := M[l := T]`.
// - Only the clause `D` can be affected, but I have that `M' |= D0`, since `M'` only touches literal `l`.
// - We also now know that `M' |= l \/ C0`, and thus `M' |= C`.
// - This means that we have that `M' |= D` and `M' |= C`, and thus `M' |= F /\ C` (the rest of `F` is unaffected).
// - The key insight was to case split on the value of `M[l]`, and then on `M |= C0 \/ D0`.
//
// #### What have we learnt?
// - It is safe to learn clauses via the RAT property.
