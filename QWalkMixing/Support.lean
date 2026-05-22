import QWalkMixing.Definitions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/--
The conjugate transpose of `U(t)` is `U(-t)`
-/
lemma U_conj_transpose {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) :
    ∀ (t : ℝ), (g.U t).conjTranspose = g.U (-t) := by
  intro t
  unfold QWalkGraph.U
  rw [←Matrix.star_eq_conjTranspose, NormedSpace.star_exp, star_smul]
  simp
  rw [Matrix.star_eq_conjTranspose, g.adjMatrix_hermitian.eq]

/--
`U` is a unitary matrix
-/
lemma U_unitary {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) :
    ∀ (t : ℝ), (g.U t) ∈ Matrix.unitaryGroup V ℂ := by
  intro t
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, U_conj_transpose]
  unfold QWalkGraph.U
  rw [←Matrix.exp_add_of_commute]
  · simp
  · simp

/--
If the adjacency matrix is symmetric, then `U` is also symmetric
-/
lemma U_on_symmetric_is_symmetric {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    (hSymm : g.adjMatrix = g.adjMatrix.transpose) :
    ∀ (t : ℝ), (g.U t) = (g.U t).transpose := by
  intro t
  unfold QWalkGraph.U
  rw [←Matrix.exp_transpose, Matrix.transpose_smul, ←hSymm]

/--
The mixing matrix `M` is a doubly stochastic matrix, meaning it is nonnegative
and all of its columns and rows sum to 1.
-/
lemma M_doublyStocastic {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) :
    ∀ (t : ℝ), (g.M t) ∈ doublyStochastic ℝ V := by
  intro t
  unfold QWalkGraph.M
  rw [mem_doublyStochastic_iff_sum]
  have hU : g.U t * (g.U t).conjTranspose = 1 := by
    have hU_unitary : g.U t ∈ Matrix.unitaryGroup V ℂ := U_unitary g t
    rw [Matrix.mem_unitaryGroup_iff] at hU_unitary
    exact hU_unitary
  have hU' : (g.U t).conjTranspose * g.U t = 1 := by
    have hU_unitary : g.U t ∈ Matrix.unitaryGroup V ℂ := U_unitary g t
    rw [Matrix.mem_unitaryGroup_iff'] at hU_unitary
    exact hU_unitary
  refine ⟨?nonneg, ?row_sums, ?col_sums⟩
  · intro i j
    apply Complex.normSq_nonneg
  · intro i -- TODO: clean this section up
    have h_test : ∀ i j, ∑ x, (g.U t i x) * star (g.U t j x) = (1 : Matrix V V ℂ) i j := by
      intro i j
      have h := congrArg (fun M => M i j) hU
      simp [Matrix.mul_apply] at h
      simp
      exact h
    simp
    specialize h_test i i
    conv at h_test =>
      lhs
      congr
      · skip
      · intro x
        simp
        rw [mul_comm, ←Complex.normSq_eq_conj_mul_self]
    simp at h_test
    apply_fun Complex.ofReal
    simp
    exact h_test
    unfold Complex.ofReal Function.Injective
    simp
  · intro j
    have h_test : ∀ i j, ∑ x, star (g.U t x i) * (g.U t x j) = (1 : Matrix V V ℂ) i j := by
      intro i j
      have h := congrArg (fun M => M i j) hU'
      simp [Matrix.mul_apply] at h
      simp
      exact h
    simp
    specialize h_test j j
    conv at h_test =>
      lhs
      congr
      · skip
      · intro x
        simp
        rw [←Complex.normSq_eq_conj_mul_self]
    simp at h_test
    apply_fun Complex.ofReal
    simp
    exact h_test
    unfold Complex.ofReal Function.Injective
    simp

/--
We have PST from `a` to `b` iff the entry at row `a` column `b` of `U`
has the value `γ` where `‖γ‖ = 1`.
-/
lemma PSTAtTimeT_phase_iff {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    (a b : V) (t : ℝ) : PSTAtTimeT g a b t ↔ ∃γ : ℂ, ‖γ‖ = 1 ∧ g.U t b a = γ := by
  unfold PSTAtTimeT
  unfold QWalkGraph.M
  simp only [Matrix.of_apply, Matrix.map_apply, ↓existsAndEq, and_true]
  constructor
  · intro hPST
    rw [Complex.normSq_eq_norm_sq, sq_eq_one_iff] at hPST
    rcases hPST with (h1 | hn1)
    · exact h1
    · exfalso
      have norm_nonneg : ‖g.U t b a‖ ≥ 0 := by apply norm_nonneg
      linarith
  · intro hPST
    rw [Complex.normSq_eq_norm_sq, sq_eq_one_iff]
    left
    exact hPST

/--
PST from `a` to `b` at time t can be equivelently formulated as `U(t)e_a = γe_b`
where `e_x` is the standard basis vector (0 everywhere exact 1 at x)
and `γ` is a phase with `‖γ‖ = 1`
-/
theorem PSTAtTimeT_vector_iff {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    (a b : V) (t : ℝ) :
    PSTAtTimeT g a b t ↔ ∃γ : ℂ, ‖γ‖ = 1 ∧ Matrix.mulVec (g.U t) (e a) = γ • (e b) := by
  constructor
  · intro hPST -- TODO: clean this section up
    have hPST' := hPST
    rw [PSTAtTimeT_phase_iff] at hPST
    unfold PSTAtTimeT QWalkGraph.M at hPST'
    simp at hPST'
    rcases hPST with ⟨γ, hγ, hU⟩
    use γ
    apply And.intro hγ
    funext i
    by_cases h : i = b
    · rw [h]
      simp
      exact hU
    · simp
      rw [Pi.single_eq_of_ne h]
      simp
      have hM : ∑ j, g.M t j a = 1 :=
        sum_col_of_mem_doublyStochastic (M_doublyStocastic g t) a
      rw [QWalkGraph.M] at hM
      simp only [Matrix.of_apply, Matrix.map_apply] at hM
      have hγ' := congrArg (fun (v : ℝ) => v^2) hγ
      simp only [one_pow] at hγ'
      rw [←RCLike.normSq_eq_def'] at hγ'
      rw [←hU] at hγ'
      apply_fun (fun (v : ℝ) => v - 1) at hM
      rw [←hγ'] at hM
      simp only [RCLike.normSq_to_complex, sub_self] at hM
      have htmp : Complex.normSq (g.U t b a) = ∑ j ∈ {b}, Complex.normSq (g.U t j a) := by
        simp
      rw [htmp] at hM
      rw [←Finset.sum_sdiff_sub_sum_sdiff] at hM
      have htmp2 : {b} \ Finset.univ = ∅ := by simp
      rw [htmp2, Finset.sum_empty, sub_zero] at hM
      have hge : ∀ i ∈ Finset.univ \ {b}, Complex.normSq (g.U t i a) ≥ 0 := by
        intro i hi
        exact Complex.normSq_nonneg (g.U t i a)
      have hle : ∀ i ∈ Finset.univ \ {b}, Complex.normSq (g.U t i a) ≤ 0 := by
        intro i hi
        have tmp := Finset.single_le_sum hge hi
        rw [hM] at tmp
        exact tmp
      have hzero : ∀ i ∈ Finset.univ \ {b}, Complex.normSq (g.U t i a) = 0 := by
        intro i hi
        exact eq_of_ge_of_le (hge i hi) (hle i hi)
      have h_i_mem : i ∈ Finset.univ \ {b} := by grind
      have tmp : Complex.normSq (g.U t i a) = 0 := hzero i h_i_mem
      rw [Complex.normSq_eq_zero] at tmp
      exact tmp
  · intro hPST
    rw [PSTAtTimeT_phase_iff]
    rcases hPST with ⟨γ, hγ, hU⟩
    use γ
    apply And.intro hγ
    have hb := congrArg (fun (v : V → ℂ) => v b) hU
    simp at hb
    exact hb

/--
PST is transitive, meaning if we have PST from `a` to `b` at time `t1` and
PST from `b` to `c` at time `t2`, then we have PST from `a` to `c` at time `t1 + t2`
-/
theorem PSTAtTimeT_trans {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    {a b c : V} {t1 t2 : ℝ} (hPSTab : PSTAtTimeT g a b t1) (hPSTbc : PSTAtTimeT g b c t2)
    : PSTAtTimeT g a c (t1 + t2) := by
  rw [PSTAtTimeT_vector_iff] at *
  rcases hPSTab with ⟨γ1, hγ1, hU1⟩
  rcases hPSTbc with ⟨γ2, hγ2, hU2⟩
  use γ1 * γ2
  simp only [Complex.norm_mul, hγ1, hγ2, mul_one, true_and]
  have hU := congrArg (fun (v : V → ℂ) => Matrix.mulVec (g.U t2) v) hU1
  simp only [] at hU
  rw [Matrix.mulVec_smul, hU2, Matrix.mulVec_mulVec] at hU
  unfold QWalkGraph.U at hU
  have h1 : (Complex.I * ↑(t1 + t2)) = (Complex.I * t2) + (Complex.I * t1) := by
    simp only [Complex.ofReal_add]
    rw [mul_add, add_comm]
  rw [←Matrix.exp_add_of_commute, ←add_smul, ←h1] at hU
  · rw [←QWalkGraph.U, smul_smul] at hU
    exact hU
  · rw [commute_iff_eq]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [smul_comm]

/--
If our graph is symmetric, then PST from `a` to `b` implies PST from `b` to `a`.
The symmetric condition is justified because there are
nonsymmetric graphs that do not have this property.
-/
theorem PSTAtTimeT_symmetric_comm {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    {a b : V} (hSymm : g.adjMatrix = g.adjMatrix.transpose) {t : ℝ} (hPST : PSTAtTimeT g a b t)
    : PSTAtTimeT g b a t := by
  rw [PSTAtTimeT_phase_iff] at *
  rcases hPST with ⟨γ, hγ, hU⟩
  use γ
  apply And.intro hγ
  rw [U_on_symmetric_is_symmetric g hSymm t, Matrix.transpose_apply]
  exact hU

/--
Any PST on a symmetric graph implies that it must periodically return to
the starting point.
-/
theorem PST_symmetric_periodic {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    {a b : V} (hSymm : g.adjMatrix = g.adjMatrix.transpose) {t : ℝ} (hPST : PSTAtTimeT g a b t)
    : PSTAtTimeT g a a (2*t) := by
  have hPST_comm : PSTAtTimeT g b a t := PSTAtTimeT_symmetric_comm g hSymm hPST
  have hPST_self : PSTAtTimeT g a a (t + t) := PSTAtTimeT_trans g hPST hPST_comm
  rw [←two_mul] at hPST_self
  exact hPST_self

--Matrix.IsHermitian.spectral_theorem

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
