import QWalkMixing.Definitions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup


--Matrix.IsHermitian.spectral_theorem

lemma U_conj_transpose {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) :
    ∀ (t : ℝ), (g.U t).conjTranspose = g.U (-t) := by
  intro t
  unfold QWalkGraph.U
  rw [←Matrix.star_eq_conjTranspose, NormedSpace.star_exp, star_smul]
  simp
  rw [Matrix.star_eq_conjTranspose, g.adjMatrix_hermitian.eq]

lemma U_unitary {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) :
    ∀ (t : ℝ), (g.U t) ∈ Matrix.unitaryGroup V ℂ := by
  intro t
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, U_conj_transpose]
  unfold QWalkGraph.U
  rw [←Matrix.exp_add_of_commute]
  · simp
  · simp

/-theorem QWalk_SpectralDecomp {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) :
  ∃ (eigenvalues : Finset ℂ) (eigenvectors : Finset (Matrix V 1 ℂ)),
    (∀ λ ∈ eigenvalues, ∃ v ∈ eigenvectors, g.adj_matrix.toEuclideanLin v = λ • v)
    ∧ (∀ v ∈ eigenvectors, ∃ λ ∈ eigenvalues, g.adjMatrix.toEuclideanLin v = λ • v)
    ∧ (∀ v w ∈ eigenvectors, v ≠ w → InnerProductSpace.isOrthonormalSet {v, w}) := by
  sorry-/

def K2 : QWalkGraph (Fin 2) :=
  QWalkGraph.of (SimpleGraph.completeGraph (Fin 2))

example : UniformMixing K2 := by
  use (Real.pi / 4)
  unfold UniformMixingAtTimeT
  simp
  /-have adj : K2.adj_matrix = ![![0, 1], ![1, 0]] := by
    unfold WeightedGraph.adj_matrix
    funext x y
    #check Fin.casesOn
    have hx : x = 0 ∨ x = 1 := by grind
    have hy : y = 0 ∨ y = 1 := by grind
    unfold K2
    unfold QWalkGraph.of
    rcases hx with (hx | hx)
    · rcases hy with (hy | hy)
      · simp [hx, hy]
      · simp [hx, hy]
    · rcases hy with (hy | hy)
      · simp [hx, hy]
      · simp [hx, hy]
  rw [adj]
  simp-/
  have K2_symm : (K2.adjMatrix.toEuclideanLin).IsSymmetric := by sorry
    --simpa using K2.adjMatrix_hermitian.isSymmetric_toEuclideanLin
  --#check LinearMap.IsSymmetric.toMatrix_eigenvectorBasis K2_symm
  sorry
