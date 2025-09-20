# Operator Algebras and States

## Gelfand-Naimark-Segal (GNS) Construction

### Definitions used

- A positive linear functional $\omega : A \to \mathbb C$ satisfies $\omega(a^*a) \ge 0$ for all $a\in A$; it is a state if $\|\omega\|=1$ (equivalently $\omega(1)=1$ in the unital case).
- A vector state on a representation $\pi : A \to B(H)$ with vector $\xi\in H$ is $a \mapsto \langle \xi, \pi(a)\xi \rangle$.
- A *-representation $\pi : A \to B(H)$ is nondegenerate if $\overline{\pi(A)H} = H$.
- A vector $\xi\in H$ is cyclic for $\pi$ if $\overline{\pi(A)\xi} = H$.

### Theorem (GNS Construction — detailed statement)

Let $A$ be a C*-algebra (not necessarily unital) and let $\omega : A \to \mathbb C$ be a state. Then there is a triple $(H_\omega, \pi_\omega, \Omega_\omega)$ with the following properties:

1) Hilbert space and representation

- $H_\omega$ is a Hilbert space obtained as the completion of $A/N_\omega$ where
	$$N_\omega := \{ a \in A : \omega(a^*a) = 0 \}$$
	and the inner product on $A/N_\omega$ is
	$$\langle [a], [b] \rangle := \omega(b^* a).$$
- $\pi_\omega : A \to B(H_\omega)$ is a nondegenerate *-representation determined on the dense subspace $A/N_\omega$ by
	$$\pi_\omega(a)[b] := [ab], \quad a,b\in A,$$
	and extends by continuity; moreover it satisfies the operator-norm estimate
	$$\|\pi_\omega(a)\| \le \|a\| \quad \text{for all } a\in A.$$

2) Cyclic vector and vector-state identity

- There exists a cyclic vector $\Omega_\omega \in H_\omega$ such that
	$$\omega(a) = \langle \Omega_\omega, \pi_\omega(a)\, \Omega_\omega \rangle \quad \text{for all } a\in A.$$
- If $A$ is unital, one can take $\Omega_\omega = [1]$; in the non-unital case one may take $\Omega_\omega = \lim_\lambda [e_\lambda]$ for any contractive approximate identity $(e_\lambda)$, or pass to the unitization and restrict back.

3) Universal property (uniqueness up to unitary)

- If $(H,\pi,\Omega)$ is any cyclic *-representation with $\omega(a)=\langle \Omega, \pi(a)\Omega\rangle$ for all $a\in A$, then there exists a unique unitary $U : H_\omega \to H$ such that
	$$U\, \pi_\omega(a) = \pi(a)\, U \quad (a\in A), \qquad U\, \Omega_\omega = \Omega.$$
- More generally, for arbitrary $(H,\pi,\Omega)$ (not necessarily cyclic), there is a unique isometry $U : H_\omega \to H$ intertwining the representations and mapping $\Omega_\omega$ to the orthogonal projection of $\Omega$ onto $\overline{\pi(A)\Omega}$, with range equal to $\overline{\pi(A)\Omega}$.

4) Standard consequences

- $N_\omega$ is a closed left ideal; $\pi_\omega$ is nondegenerate; $\|\Omega_\omega\|^2 = \|\omega\| = 1$ in the unital case.
- $\omega$ is faithful if and only if $N_\omega=\{0\}$, in which case $\pi_\omega$ is faithful.
- $\omega$ is pure if and only if $\pi_\omega$ is irreducible. In the unital case and for pure $\omega$, one has $\pi_\omega(A)'' = B(H_\omega)$.

This yields a canonical way to realize every state as a vector state in a cyclic *-representation of $A$, connecting abstract C*-algebras to concrete operator algebras on Hilbert spaces.

### Detailed statement and properties

Let $A$ be a C*-algebra (not necessarily unital), and let $\omega : A \to \mathbb{C}$ be a state, i.e. a positive linear functional with $\|\omega\| = 1$ (equivalently, in the unital case $\omega(1)=1$ and $\omega(a^*a)\ge 0$ for all $a$).

1) Pre-Hilbert space and null space

- Define the seminorm $p_\omega(a) := \sqrt{\omega(a^* a)}$ and the left kernel (null space)
	$$N_\omega := \{ a \in A : \omega(a^* a) = 0 \}.$$
- Then $N_\omega$ is a left ideal in $A$. In fact, for any $x \in A$ and $a \in N_\omega$,
	$$\omega((xa)^*(xa)) = \omega(a^* x^* x a) \le \|x^*x\|\, \omega(a^* a) = 0,$$
	hence $xa \in N_\omega$.
- Define an inner product on the quotient $A/N_\omega$ by
	$$\langle [a], [b] \rangle := \omega(b^* a).$$
	This is well-defined (if $a'\sim a$ and $b'\sim b$, then $\omega(b'^* a')=\omega(b^* a)$), conjugate-linear in the first variable and linear in the second, and positive definite: $\langle [a],[a]\rangle = \omega(a^* a) \ge 0$, and equals $0$ iff $[a]=0$.
- Denote by $H_\omega$ the Hilbert space completion of $A/N_\omega$ for this inner product.

2) Representation and cyclic vector

- For $a\in A$, define $\pi_\omega(a): A/N_\omega \to A/N_\omega$ by $\pi_\omega(a)[b] := [ab]$. This is well-defined because $N_\omega$ is a left ideal.
- $\pi_\omega(a)$ extends by continuity to a bounded operator on $H_\omega$, with $\|\pi_\omega(a)\| \le \|a\|$; furthermore $\pi_\omega$ is a *-homomorphism: $\pi_\omega(ab)=\pi_\omega(a)\pi_\omega(b)$ and $\pi_\omega(a^*)=\pi_\omega(a)^*$, and is non-degenerate (i.e., $\overline{\pi_\omega(A)H_\omega}=H_\omega$).
- If $A$ is unital, define the cyclic vector $\Omega_\omega := [1] \in H_\omega$; then $\overline{\pi_\omega(A)\Omega_\omega}=H_\omega$.
- For nonunital $A$, one can either pass to the unitization $\tilde A$ and restrict back, or use an approximate identity $(e_\lambda)$ and let $\Omega_\omega$ be the limit of $[e_\lambda]$ in $H_\omega$; in either case, one obtains a cyclic vector realizing $\omega$ as a vector state.

3) Vector state identity and norm

- For all $a \in A$, one has
	$$\omega(a) = \langle \Omega_\omega, \, \pi_\omega(a)\, \Omega_\omega \rangle.$$
- In the unital case, $\|\omega\| = \omega(1) = \|\Omega_\omega\|^2 = 1$.

4) Universality (uniqueness up to unitary equivalence)

- If $(H,\pi,\Omega)$ is any cyclic *-representation of $A$ with $\omega(a) = \langle \Omega, \pi(a) \Omega\rangle$ for all $a$, then there exists a unique unitary $U : H_\omega \to H$ such that
	$$U\, \pi_\omega(a) = \pi(a)\, U \quad \text{for all } a\in A, \qquad U\, \Omega_\omega = \Omega.$$
- Consequently, the GNS triple $(H_\omega, \pi_\omega, \Omega_\omega)$ is unique up to unitary equivalence among all cyclic realizations of $\omega$.

5) Standard corollaries

- Faithfulness: If $\omega$ is faithful (i.e., $\omega(a^* a)=0 \Rightarrow a=0$), then $N_\omega=\{0\}$ and $\pi_\omega$ is faithful (injective *-representation).
- Purity: $\omega$ is a pure state if and only if $\pi_\omega$ is irreducible (its commutant is $\mathbb{C} I$). In the unital case, for pure $\omega$ one has $\pi_\omega(A)'' = B(H_\omega)$.
- Normality at the von Neumann closure: The vector state $a \mapsto \langle \Omega_\omega, \pi_\omega(a)\Omega_\omega\rangle$ extends uniquely to a normal state on the von Neumann algebra $\pi_\omega(A)''$.

6) Remarks and variants

- The construction is functorial for states under *-isomorphisms: a *-isomorphism $\alpha : A \to B$ sends $\omega$ to $\omega\circ \alpha^{-1}$, and the corresponding GNS representations are unitarily equivalent via the induced map.
- For weights (possibly unbounded positive linear functionals), a GNS-like construction exists with a suitable domain and closable representation; this generalizes the state case but requires additional analytic care.

### Proof sketches and useful estimates

1) Cauchy–Schwarz for positive functionals

- If $\omega$ is positive, then for all $a,b\in A$ one has
	$$|\omega(b^* a)|^2 \le \omega(a^* a)\, \omega(b^* b).$$
	Proof sketch: For any $\lambda\in \mathbb C$, positivity of $\omega$ on $(a+\lambda b)^*(a+\lambda b)$ gives a quadratic polynomial in $\lambda$ with nonnegative discriminant, yielding the inequality.

2) Left ideal and well-defined inner product

- Using Cauchy–Schwarz, if $a\in N_\omega$ then for any $x\in A$
	$$\omega((xa)^*(xa)) = \omega(a^* x^* x a) \le \|x^*x\|\, \omega(a^* a) = 0,$$
	so $xa\in N_\omega$ and $N_\omega$ is a left ideal.
- If $a' = a + n_1$ and $b' = b + n_2$ with $n_i \in N_\omega$, then
	$$\omega(b'^* a') = \omega((b+n_2)^*(a+n_1)) = \omega(b^* a) + \omega(n_2^* a) + \omega(b^* n_1) + \omega(n_2^* n_1) = \omega(b^* a)$$
	because $\omega(n_2^* a)=\overline{\omega(a^* n_2)}=0$ and similarly for the others by Cauchy–Schwarz and $\omega(n^* n)=0$.

3) Boundedness and *-homomorphism property of $\pi_\omega$

- For $[b]\in A/N_\omega$,
	$$\|\pi_\omega(a)[b]\|^2 = \omega((ab)^*(ab)) = \omega(b^* a^* a b)
	\le \|a^* a\|\, \omega(b^* b) = \|a\|^2 \|[b]\|^2,$$
	hence $\|\pi_\omega(a)\| \le \|a\|$. Algebra gives $\pi_\omega(ab)=\pi_\omega(a)\pi_\omega(b)$ and $\pi_\omega(a^*)=\pi_\omega(a)^*$.

4) Cyclicity and non-degeneracy

- In the unital case, $[b]=\pi_\omega(b)[1]=\pi_\omega(b)\Omega_\omega$, so $\{\pi_\omega(a)\Omega_\omega : a\in A\}$ is dense; this shows cyclicity and non-degeneracy. In the nonunital case, approximate units give the same conclusion.

5) Explicit unitary in the universality statement

- Given a cyclic realization $(H,\pi,\Omega)$ of $\omega$, define $U_0 : A/N_\omega \to H$ by $U_0([a]) := \pi(a)\Omega$. Then by the inner product identity $\langle [a],[b]\rangle = \langle \pi(a)\Omega, \pi(b)\Omega\rangle$, $U_0$ is an isometry with dense range, hence extends to a unitary $U : H_\omega \to \overline{\pi(A)\Omega} = H$ and satisfies $U\,\pi_\omega(a)=\pi(a)\,U$ and $U\Omega_\omega=\Omega$.

6) Nonunital variants: unitization vs approximate identity

- Unitization: Let $\tilde A$ be the minimal unitization. Define $\tilde\omega(a, \lambda) := \omega(a) + \lambda$; then apply GNS to $(\tilde A, \tilde\omega)$, and restrict to $A$ to obtain a cyclic *-representation and a cyclic vector realizing $\omega$.
- Approximate identity: Let $(e_\lambda)$ be a contractive approximate identity. Then $([e_\lambda])$ is Cauchy in $H_\omega$ and converges to a vector $\Omega_\omega$ with $\omega(a)=\langle \Omega_\omega, \pi_\omega(a)\Omega_\omega\rangle$.

7) Commutative case $A = C_0(X)$ (Riesz representation)

- By Riesz–Markov–Kakutani, a state $\omega$ on $C_0(X)$ corresponds to a probability measure $\mu$ on $X$ via $\omega(f)=\int f\, d\mu$. The GNS Hilbert space is $H_\omega = L^2(X,\mu)$, the representation is pointwise multiplication $(\pi_\omega(f)\xi)(x) = f(x)\,\xi(x)$, and the cyclic vector is $\Omega_\omega = \mathbf 1 \in L^2(X,\mu)$, with $\omega(f)=\langle \Omega_\omega, \pi_\omega(f)\Omega_\omega\rangle$.


