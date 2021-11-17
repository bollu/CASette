# CASette: Computer Algebra System algorithms

#### Algorithms
- [multivariate polynomial division](./division.py) to compute multivariate reminder term.
- [schrier sims algorithm](./schrier-sims.py) to compute a good representation of subgroups of the symmetric group. Formally,
  compute a strong generating set.
- [todd coxeter algorithm](./todd-coxeter.py) to compute the permutation representation of the cosets of a subgroup. Formally,
  build the schrier graph and extract the coset table.
- [Bucchberger algorithm](./bucchberger.py) to computing grobner basis of ideal.
- [Fundamental theorem of symmetric polynomials](./ftsp.cpp) to write a given
  symmetric polynomial in terms of elementary symmetric polynomials.
- [Plucker coordinates](./plucker.py) implements common graphics operations via plucker coordinates, as a step to
  understand the grassmanian

#### Aspirational algorithms
- [Schubert decomposition of the grassmanian](./grassman.py) to compute the cohomology of the grassmanian.
- [Algorithms on tableaux](./tableaux.cpp) in particular, implement RSK to show the RSK correspondence, and also implement the fourier transform
  on the symmetric group.

#### Books
- Bijective combinatorics: Chapter on Tableaux.
- [SnoB: FFT for the symmetric group](http://people.cs.uchicago.edu/~risi/SnOB/index.html)
- FTSP: Fundamental theorem of symmetric polynomials
- Ideals, Varieties, Algorithms
- [Serees: Permutation group algorithms](https://doc.lagout.org/science/0_Computer%20Science/2_Algorithms/Permutation%20Group%20Algorithms%20%5BSeress%202003-03-17%5D.pdf)



#### Notes
- [intuition for why symmetric polynomials are important](./reading/symmetric-polynomials.md)

