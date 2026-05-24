import QWalkMixing.Definitions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/--
The conjugate transpose of `U(t)` is `U(-t)`
-/
lemma U_conj_transpose {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) :
    ∀ (t : ℝ), (g.U t).conjTranspose = g.U (-t) := by
  intro t
  unfold QWalkGraph.U
  rw [←Matrix.star_eq_conjTranspose, NormedSpace.star_exp, star_smul]
  rw [Matrix.star_eq_conjTranspose, g.adjMatrix_hermitian.eq]
  simp

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
  have hU  : g.U t * (g.U t).conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp  (U_unitary g t)
  have hU' : (g.U t).conjTranspose * g.U t = 1 := Matrix.mem_unitaryGroup_iff'.mp (U_unitary g t)
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?nonneg, ?row_sums, ?col_sums⟩
  · intro i j
    apply Complex.normSq_nonneg
  · intro i
    have hRowSum : ∑ x, (g.U t i x) * star (g.U t i x) = 1 := by
      have h := congrArg (fun M => M i i) hU
      simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
      rw [RCLike.star_def]
      exact h
    simp only [Matrix.of_apply, Matrix.map_apply]
    conv_lhs at hRowSum =>
      rhs
      intro x
      rw [mul_comm, RCLike.star_def, ←Complex.normSq_eq_conj_mul_self]
    norm_cast at hRowSum
  · intro j
    have hColSum : ∑ x, star (g.U t x j) * (g.U t x j) = 1 := by
      have h := congrArg (fun M => M j j) hU'
      simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
      rw [RCLike.star_def]
      exact h
    simp only [Matrix.of_apply, Matrix.map_apply]
    conv_lhs at hColSum =>
      rhs
      intro x
      rw [RCLike.star_def, ←Complex.normSq_eq_conj_mul_self]
    norm_cast at hColSum

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
where `e_x` is the standard basis vector (0 everywhere except 1 at x)
and `γ` is a phase with `‖γ‖ = 1`
-/
theorem PSTAtTimeT_vector_iff {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    (a b : V) (t : ℝ) :
    PSTAtTimeT g a b t ↔ ∃γ : ℂ, ‖γ‖ = 1 ∧ Matrix.mulVec (g.U t) (e a) = γ • (e b) := by
  constructor
  · intro hPST
    rw [PSTAtTimeT_phase_iff] at hPST
    rcases hPST with ⟨γ, hγ, hU⟩
    refine ⟨γ, hγ, ?_⟩
    funext i
    by_cases hi : i = b
    · rw [hi]
      simpa
    · simp only [e, Matrix.mulVec_single, MulOpposite.op_one, Pi.smul_apply,
                Matrix.col_apply, one_smul, smul_eq_mul]
      rw [Pi.single_eq_of_ne hi, mul_zero]
      have hM : ∑ j, g.M t j a = 1 :=
        sum_col_of_mem_doublyStochastic (M_doublyStocastic g t) a
      simp only [QWalkGraph.M, Matrix.of_apply, Matrix.map_apply] at hM
      have hγ' := congrArg (fun (v : ℝ) => v^2) hγ
      simp only [one_pow] at hγ'
      rw [←RCLike.normSq_eq_def', RCLike.normSq_to_complex, ←hU] at hγ'
      have hb_in_V : b ∈ (@Finset.univ V _) := by grind
      rw [←Finset.add_sum_erase Finset.univ _ hb_in_V, hγ', add_eq_left] at hM
      have h_norm_nonneg : ∀ i ∈ Finset.univ.erase b, Complex.normSq (g.U t i a) ≥ 0 := by
        intro i hi
        exact Complex.normSq_nonneg (g.U t i a)
      have h_i_mem : i ∈ Finset.univ.erase b := by grind
      have h_norm_nonpos : Complex.normSq (g.U t i a) ≤ 0 := by
        have := Finset.single_le_sum h_norm_nonneg h_i_mem
        linarith
      exact Complex.normSq_eq_zero.mp
        (eq_of_ge_of_le (h_norm_nonneg i h_i_mem) h_norm_nonpos)
  · intro hPST
    rw [PSTAtTimeT_phase_iff]
    rcases hPST with ⟨γ, hγ, hU⟩
    refine ⟨γ, hγ, ?_⟩
    have := congrArg (fun (v : V → ℂ) => v b) hU
    simpa

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
  rw [←Matrix.exp_add_of_commute] at hU
  · rw [←add_smul, ←h1, ←QWalkGraph.U, smul_smul] at hU
    exact hU
  · rw [commute_iff_eq]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [smul_comm]

/--
If our graph is symmetric, then PST from `a` to `b` implies PST from `b` to `a` (it commutes).
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

/-- The orthogonal projector onto the `μ`-eigenspace of a Hermitian matrix `A`,
expressed as a matrix: the sum of rank-one outer products `uᵢ uᵢ*` over the
eigenvectors `uᵢ` whose eigenvalue equals `μ`. -/
noncomputable def eigenProj {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian) (μ : ℝ) : Matrix V V ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i = μ),
    Matrix.vecMulVec (hA.eigenvectorBasis i) (star (hA.eigenvectorBasis i))

/-- **Spectral decomposition of a Hermitian matrix.** A Hermitian matrix `A` is
equal to the sum, over its distinct eigenvalues `μ`, of `μ` times the orthogonal
projector onto the `μ`-eigenspace. -/
theorem isHermitian_spectral_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian) :
    A = ∑ μ ∈ (Set.range hA.eigenvalues).toFinset, (μ : ℂ) • eigenProj hA μ := by
  -- Reduce to entry-wise equality.
  ext j k
  -- Rewrite the RHS at entry `(j, k)` as a double sum over eigenvalues and the
  -- eigenvectors carrying them. Pull the scalar `μ` inside the inner sum and
  -- replace it with `hA.eigenvalues i` using the filter hypothesis.
  have rhs_eq :
      (∑ μ ∈ (Set.range hA.eigenvalues).toFinset, ((μ : ℂ) • eigenProj hA μ)) j k
        = ∑ μ ∈ (Set.range hA.eigenvalues).toFinset,
            ∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i = μ),
              (hA.eigenvalues i : ℂ) *
                (hA.eigenvectorBasis i j * star (hA.eigenvectorBasis i k)) := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
               eigenProj, Matrix.vecMulVec_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  rw [rhs_eq]
  -- Collapse the double sum into a single sum over all eigenvector indices:
  -- every `i ∈ univ` belongs to exactly one fiber `{i | eigenvalues i = μ}`.
  rw [Finset.sum_fiberwise_of_maps_to
        (t := (Set.range hA.eigenvalues).toFinset)
        (g := hA.eigenvalues)
        (by intro i _; rw [Set.mem_toFinset]; exact Set.mem_range_self i)]
  -- Read off `A j k` from the spectral theorem `A = U D U*`.
  have h_spectral := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spectral
  have h_entry : A j k = ∑ i,
      (hA.eigenvectorUnitary : Matrix V V ℂ) j i *
        (hA.eigenvalues i : ℂ) *
        star ((hA.eigenvectorUnitary : Matrix V V ℂ) k i) := by
    conv_lhs => rw [h_spectral]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
               Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- The inner sum collapses: only the diagonal term at index `i` survives.
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp only [mul_ite, mul_zero, ite_eq_right_iff]
      intro h
      exact absurd h hb
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h_entry]
  -- Match term by term: column `i` of `eigenvectorUnitary` is the `i`-th eigenvector.
  refine Finset.sum_congr rfl fun i _ => ?_
  have hU_eq : ∀ (a b : V),
      (hA.eigenvectorUnitary : Matrix V V ℂ) a b = hA.eigenvectorBasis b a :=
    fun _ _ => rfl
  rw [hU_eq, hU_eq]
  ring

theorem U_spectral_decomp {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) (t : ℝ) :
    g.U t = ∑ μ ∈ (Set.range g.adjMatrix_hermitian.eigenvalues).toFinset,
    NormedSpace.exp (Complex.I * t * ↑μ) • eigenProj g.adjMatrix_hermitian μ := by
  unfold QWalkGraph.U
  have hA_decomp: g.adjMatrix = ∑ μ ∈ (Set.range g.adjMatrix_hermitian.eigenvalues).toFinset,
      (μ : ℂ) • eigenProj g.adjMatrix_hermitian μ
    := isHermitian_spectral_decomposition g.adjMatrix_hermitian
  --#check NormedSpace.exp_analytic
  let f : ℝ -> (Matrix V V ℂ):= fun x => (Complex.I * ↑t * ↑x) • eigenProj g.adjMatrix_hermitian x
  have test : ∀ x, f x = (Complex.I * ↑t * ↑x) • eigenProj g.adjMatrix_hermitian x := by
    intro x
    unfold f
    rfl
  conv_lhs =>
    rw [hA_decomp]
    rw [Finset.smul_sum]
    congr
    rhs
    intro x
    rw [smul_smul, ←(test x)]
  conv_lhs =>
    simp
    rw [Matrix.exp_sum_of_commute
        (Finset.image g.adjMatrix_hermitian.eigenvalues Finset.univ)
        f (by sorry)]
    unfold f
    /-congr
    · skip
    · intro i
      rw [Matrix.exp_nsmul (Complex.I * ↑t * ↑x)]-/
  sorry
  --simp


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
