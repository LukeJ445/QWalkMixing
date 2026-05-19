import QWalkMixing.Support

open Complex

-- Formal proofs of results in "Uniform Mixing in Chiral Quantum Walks"
-- https://arxiv.org/abs/2605.04414


-- Section 3
/-
Theorem 2. Let X be a graph of order n whose Hermitian adjacency matrix A has zero as
a simple eigenvalue with the corresponding eigenvector 1n. Then, bX has uniform mixing in
expected n3/2 time.
-/


/-
Corollary 1. For any n ≥ 2, there is a unitary signing σ so that the
complete graph K^σ_n
has uniform mixing (in expected n^3/2 time).
-/


/-
Corollary 2. For any n ≥ 1, K1,n has probabilistic uniform mixing in expected n^3/2 time.
-/

/-
Corollary 3. For any nonsingular Eulerian graph X, bX has probabilistic uniform mixing.
-/

/-
Corollary 4. For any connected graph X, the integer-weighted graph \widehat{L(X)} has probabilistic
uniform mixing.
-/

-- Section 4
/-
Claim 2. There is a signing σ of K4 so that Kσ
4 has uniform mixing at π/3√3.
-/
theorem K4_uniform_mixing : ∃ g : QWalkGraph (Fin 4),
    g.Adj = (SimpleGraph.completeGraph (Fin 4)).Adj
    ∧ UniformMixingAtTimeT g (π / (3 * Real.sqrt 3)) := by
  -- our signing of K4 is given by the following matrix:
  let σ : Matrix (Fin 4) (Fin 4) ℂ := !![
    0, -I, -I, -I;
    I,  0, -I,  I;
    I,  I,  0, -I;
    I, -I,  I,  0;
  ]
  -- it is Hermetian (check by brute force)
  have σ_hermitian : Matrix.IsHermitian σ := by
    ext i j;
    fin_cases i <;> fin_cases j <;> simp [σ]
  -- we can view this as a QWalkGraph
  let Kσ : QWalkGraph (Fin 4) := {
    weight := σ
    adjMatrix_hermitian := σ_hermitian
  }
  use Kσ
  -- it is a signing of K4 (check by brute force)
  have Kσ_complete : Kσ.Adj = (SimpleGraph.completeGraph (Fin 4)).Adj := by
    ext i j;
    fin_cases i <;> fin_cases j <;> simp [Kσ, SimpleGraph.completeGraph, σ]
  use Kσ_complete
  -- prove uniform mixing at time π/3√3
  unfold UniformMixingAtTimeT
  intro U_t
  sorry

#check SimpleGraph (Fin 4)

/-
Theorem 3. For n ≥ 1, there is a signed H(n, 4) with uniform mixing at time π/3√3.
-/

-- Section 5
/-
Theorem 5. Any (Z/nZ)-circulant with distinct eigenvalues has average uniform mixing.
-/

/-
Corollary 5. The oriented odd-cycle has average uniform mixing.
-/

/-
Corollary 6. For any n ≥ 2, the oriented skew (Z/nZ)-circulant (corresponding to the
transitive tournament) has average uniform mixing.
-/

/-
Corollary 7. Any (Z/nZ)-circulant with universal perfect state transfer has average uniform
mixing.
-/

/-
Theorem 7. (Babai [4])
Let X = Γ(G, S) be a Cayley graph over a finite group G with a connection set S where
S = S−1 (S is closed under taking inverses) and 1̸ ∈ S (X has no self-loops). Then,
1. A(X) = P
g∈S R(g) where R(g) is the left-regular representation of G.
2. There is a unitary matrix U so that U †A(X)U is a diagonal matrix with entriesP
g∈S Rρ(g) (repeated dρ times) for each irreducible representation ρ of G.
3. The eigenvalues of A(X) are given by the eigenvalues of P
g∈S Rρ(g) (each repeated dρ
times).
-/

/-
Corollary 8. Let X = Γ(G, S) be the Cayley graph of a nonabelian finite group G with an
inverse-closed connection set S which does not contain the identity. Then, X has no average
uniform mixing.
-/
