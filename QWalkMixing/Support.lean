import QWalkMixing.Definitions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic

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

lemma U_on_symmetric_is_symmetric {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    (hSymm : g.adjMatrix = g.adjMatrix.transpose) :
    ∀ (t : ℝ), (g.U t) = (g.U t).transpose := by
  intro t
  unfold QWalkGraph.U
  rw [←Matrix.exp_transpose, Matrix.transpose_smul, ←hSymm]

theorem PSTAtTimeT_iff {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) (a b : V) (t : ℝ) :
    PSTAtTimeT g a b t ↔ ∃γ : ℂ, ‖γ‖ = 1 ∧ g.U t a b = γ := by
  unfold PSTAtTimeT
  unfold QWalkGraph.M
  simp only [HadamardProduct, RCLike.star_def, Matrix.map_apply]
  constructor
  · intro hPST
    simp only [↓existsAndEq, and_true]
    have h1 : ‖g.U t a b * (starRingEnd ℂ) (g.U t a b)‖ = 1 := by
      rw [hPST]
      simp
    rw [Complex.norm_mul, Complex.norm_conj, ←sq, sq_eq_one_iff] at h1
    rcases h1 with (h1 | hn1)
    · exact h1
    · exfalso
      have norm_nonneg : ‖g.U t a b‖ ≥ 0 := by apply norm_nonneg
      linarith
  · intro hPST
    rcases hPST with ⟨γ, hγ, hU⟩
    rw [hU]
    rw [Complex.norm_eq_one_iff] at hγ
    rcases hγ with ⟨θ, hθ⟩
    rw [←hθ, ←Complex.exp_conj, ←Complex.exp_add]
    simp

theorem PSTAtTimeT_trans {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    {a b c : V} {t1 t2 : ℝ} (hPSTab : PSTAtTimeT g a b t1) (hPSTbc : PSTAtTimeT g b c t2)
    : PSTAtTimeT g a c (t1 + t2) := by
  rw [PSTAtTimeT_iff] at *
  rcases hPSTab with ⟨γ1, hγ1, hU1⟩
  rcases hPSTbc with ⟨γ2, hγ2, hU2⟩
  use γ1 * γ2
  simp [hγ1, hγ2]
  unfold QWalkGraph.U
  have h1 : (Complex.I * ↑(t1 + t2)) = (Complex.I * t1) + (Complex.I * t2) := by
    simp
    rw [mul_add]
  rw [h1, add_smul, Matrix.exp_add_of_commute]
  rw [←QWalkGraph.U, ←QWalkGraph.U]
  rw [←hU1, ←hU2]
  rw [Matrix.mul_apply]
  sorry
  sorry




  /-
  rw [PSTAtTimeT_iff] at *
  rcases hPST with ⟨γ, hγ, hU⟩
  rcases hPST' with ⟨γ', hγ', hU'⟩
  have h1 : γ = γ' := by
    rw [U_on_symmetric_is_symmetric g hSymm t, Matrix.transpose_apply] at hU
    rw [←hU, ←hU']
  use γ^2
  simp [hγ]
  unfold QWalkGraph.U
  have h2 : (Complex.I * ↑(2 * t)) = (Complex.I * t) + (Complex.I * t) := by
    simp
    rw [mul_comm, two_mul]
    grind
  rw [h2, add_smul, Matrix.exp_add_of_commute]
  --rw [←hU]
  -/

theorem PSTAtTimeT_symmetric_comm {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    {a b : V} (hSymm : g.adjMatrix = g.adjMatrix.transpose) {t : ℝ} (hPST : PSTAtTimeT g a b t)
    : PSTAtTimeT g b a t := by
  rw [PSTAtTimeT_iff] at *
  rcases hPST with ⟨γ, hγ, hU⟩
  use γ
  apply And.intro hγ
  rw [U_on_symmetric_is_symmetric g hSymm t, Matrix.transpose_apply]
  exact hU

theorem PST_symmetric_periodic {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    {a b : V} (hSymm : g.adjMatrix = g.adjMatrix.transpose) {t : ℝ} (hPST : PSTAtTimeT g a b t)
    : PSTAtTimeT g a a (2*t) := by
  have hPST_comm : PSTAtTimeT g b a t := PSTAtTimeT_symmetric_comm g hSymm hPST
  have hPST_self : PSTAtTimeT g a a (t + t) := PSTAtTimeT_trans g hPST hPST_comm
  rw [←two_mul] at hPST_self
  exact hPST_self

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
