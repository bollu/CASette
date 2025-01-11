# CASette: Computer Algebra System algorithms

#### Algorithms
- [egg](./egg/egg.py), a minimal implementation of a e-graph and E-matching.
  We do not yet implement the bytecode interpreter as explained by the z3 e-matching paper.
- [Exists Forall solver for bitvector problems](./exists-forall-yices/solver.cpp)
- [A solver for the theory commutative semigroups](./little-engines-of-proof/commsemigroup.cpp),
  which has the key insight of bucchberger's algorithm, which is to build the rewrite that equates
  [critical pair](https://www.inf.ed.ac.uk/teaching/courses/ar/slides13.pdf) for terms,
  and to then order the equation to get a termnating rewrite system.
- [multivariate polynomial division](./division.py) to compute multivariate reminder term.
- [Bucchberger algorithm](./bucchberger.py) to computing grobner basis of ideal.
- [schrier sims algorithm](./schrier-sims.py) to compute a good representation of subgroups of the symmetric group. Formally,
  compute a [base and strong generating set](https://en.wikipedia.org/wiki/Schreier%E2%80%93Sims_algorithm).
- [todd coxeter algorithm](./todd-coxeter.py) to compute the permutation representation of the cosets of a subgroup. Formally,
  build the schrier graph and extract the coset table.
- [Fundamental theorem of symmetric polynomials](./ftsp.cpp) to write a given
  symmetric polynomial in terms of elementary symmetric polynomials.
- [Plucker coordinates](./plucker.py) implements common graphics operations via plucker coordinates, as a step to
  understand the grassmanian

#### Aspirational algorithms
- [Cutting to the chase](./cut-to-the-chase.py), a decision procedure for LIA that can show UNSATs of 
  large, complex systems of integer linear problems.
- [Hormander's algorithm](./hormander/solver.cpp), a quantifier elimination procedure for real closed fields
  that is fast enough to be proof producing 'in practice' for HOL light.
- [Shostak's algorithm](./shostak/solver.cpp) for combining theories in a way that is different from Nelson Oppen.
- [Schubert decomposition of the grassmanian](./grassman.py) to compute the cohomology of the grassmanian.
- [Algorithms on tableaux](./tableaux.cpp) in particular, implement RSK to show the RSK correspondence, and also implement the fourier transform
  on the symmetric group.
- [Monster](./monster.py) computing products of elements in the monster group.

#### Books
- Bijective combinatorics: Chapter on Tableaux.
- [SnoB: FFT for the symmetric group](http://people.cs.uchicago.edu/~risi/SnOB/index.html)
- FTSP: Fundamental theorem of symmetric polynomials
- Ideals, Varieties, Algorithms
- [Serees: Permutation group algorithms](https://doc.lagout.org/science/0_Computer%20Science/2_Algorithms/Permutation%20Group%20Algorithms%20%5BSeress%202003-03-17%5D.pdf)
- Decision Procedures: An algorithmic point of view



#### Notes
- [intuition for why symmetric polynomials are important](./reading/symmetric-polynomials.md)

