- Bijective combinatorics: Chapter on Tableaux.
- [SnoB: FFT for the symmetric group](http://people.cs.uchicago.edu/~risi/SnOB/index.html)
- FTSP: Fundamental theorem of symmetric polynomials


- Any symmetric polynomial of the roots of $f(x)$ MUST BE expressible as a polynomial in the coefficients of the polynomial $f(x)$, since the
  coefficients of $f(x)$ are the elementary symmetric functions of the roots, and any symmetric function of the roots is expressible in terms
  of elementary symmetric functions (via FTSP)

- Thus, Discriminant can be written in terms of roots, since discriminant is symmetric in the roots. Recall, discriminant is zero iff
  polynomial and its root vanish. More explicitly, discriminant is the square of the difference between the roots:
  $D(p) = \sum_{i < j} (r_i - r_j)^2$.
- In the case of the quadratic, $\sqrt{D(p)}$ is the difference of the roots, and $\sigma_1(p)$ is the sum of the roots. We can deduce the roots
  from these two quantities.

- Given a polynomial $f$ (ie, given the coefficients of $x^i$ in $f$)
  with roots $\{ r_i \}$ (where the roots are unknown), can one create a polynomial with roots $\{ r_i^2 \}$, $\{ r_i^3 \}$
  and so on?

- TODO: mediate on why the "difference in exponents" of symmetric polynomials gives us power sum. There is something interesting going on here,
  at least in terms of "mental modesls".

- Spreadness of a monomial $x_1^{k_1} \dots x_n^{k_n}$ is $\sum_i k_i^2$. Can be used instead of lex ordering in FTSP proof!


- FSTP for rational functions: any rational function that is symmetric in variables $\{ x_i \}$ is a rational function of the elementary
  symmetric functions.

- Weakening/generalization of FSTP by galois: If f is a rational function of $x_1, \dots, x_n$ that is symmetric under all permutations of
  the $x_i$ which fix $x_1$, then it is expressible as a rational function of $\sigma_1, \dots, \sigma_n$ and $x_1$.


- If $V$ is a rational function of $x_1, \dots, x_n$ that is not fixed by all nontrivial permutations of the $x_i$, then *every* rational
  function of the $x_i$ is expressible as a rational function of the $\sigma_i$ and the $V$.

- FTGT (fundamental theorrem of galois theory): Let $f$ be a polynomial with coefficients $\{ c_i \}$. Let $\{ r_i \}$ be its
  roots. Let $\{ u_i \}$ be numbers which are given by rational functions of the $\{ r_i \}$. Then there exists a group $G$
  of permutations of the $\{ r_i \}$ such that the sets (a) and (b) are equal, where these are :
  (a) rational functions of $\{ r_i \}$ fixed by the action of $G$, and 
  (b) functions whose values at the roots are expressible as rational functions of $\{ c_i \}$ and $\{ u_i \}$.
- In terms of modern language, consider the field formed by $Q(c_i)$ [the coefficient field] and $Q(r_i)$ [the splitting field].
  The set of rational functions $Q(c_i, u_i)$ is some extension of $Q(c_i)$ contained in the splitting field. So we have a tower
  of extensions $Q(c_i) \subseteq Q(c_i, u_i) \subseteq Q(r_i)$. Now, we claim that there exists a group $H$  (a subgroup of the galois
   group $Gal(Q(r_i, c_i)/Q(c_i))$) which fixes $Q(c_i, u_i)$. This $H$ is a permutation of the roots of $\{ r_i \}$ which fixes $Q(c_i, u_i)$.
  

- Resolvents by Wildberger (TODO): watch!
- On the computation of resolvents and Galois groups
- Galois for 21st century readers: https://www.ams.org/notices/201207/rtx120700912p.pdf
- Galois Theory for Beginners: A Historical Perspective

