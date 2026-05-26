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

/-- The orthogonal projector onto the `μ`-eigenspace of a Hermitian matrix `A`,
expressed as a matrix: the sum of rank-one outer products `uᵢ uᵢ*` over the
eigenvectors `uᵢ` whose eigenvalue equals `μ`. -/
noncomputable def eigenProj {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian) (μ : ℝ) : Matrix V V ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i = μ),
    Matrix.vecMulVec (hA.eigenvectorBasis i) (star (hA.eigenvectorBasis i))

lemma eigenProj_trivial {V : Type} [Fintype V] [DecidableEq V] {A : Matrix V V ℂ}
    (hA : A.IsHermitian) {μ : ℝ} (hμ : μ ∉ (Set.range hA.eigenvalues).toFinset)
    : eigenProj hA μ = 0 := by
  have hNotEigenvalue : Finset.univ.filter (fun i => hA.eigenvalues i = μ) = ∅ := by
    grind
  unfold eigenProj
  rw [hNotEigenvalue, Finset.sum_empty]

/--
Eigen projectors are idempotent (`E^2 = E`)
-/
lemma eigenProj_idem {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian)
    : ∀ μ, eigenProj hA μ * eigenProj hA μ = eigenProj hA μ := by
  intro μ
  unfold eigenProj
  rw [Finset.sum_mul_sum, Finset.sum_congr (by rfl)]
  intro a ha
  rw [←Finset.sum_erase_add (Finset.univ.filter (fun j => hA.eigenvalues j = μ)) _ ha]
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hOrtho := hA.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at hOrtho
  specialize hOrtho a a
  simp only [↓reduceIte] at hOrtho
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hOrtho
  rw [hOrtho]
  simp only [one_smul, add_eq_right]
  rw [Finset.sum_eq_zero ?_]
  intro x hx
  have hax : a ≠ x := by grind
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hOrtho' := hA.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at hOrtho'
  specialize hOrtho' a x
  simp only [hax, ↓reduceIte] at hOrtho'
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hOrtho'
  rw [hOrtho']
  simp

/--
Eigen projectors are orthagonal (`E₁*E₂ = 0`)
-/
lemma eigenProj_orthag {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian)
    : ∀ a b, a ≠ b → eigenProj hA a * eigenProj hA b = 0 := by
  intro a b hab
  unfold eigenProj
  rw [Finset.sum_mul_sum, Finset.sum_eq_zero ?_]
  intro i hi
  rw [Finset.sum_eq_zero ?_]
  intro j hj
  have hij : i ≠ j := by grind
  rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm,
      ←EuclideanSpace.inner_eq_star_dotProduct,
      Orthonormal.inner_eq_zero hA.eigenvectorBasis.orthonormal hij]
  simp

/--
`Ea*Eb` = `E` if `a = b` and `0` if `a ≠ b`
-/
lemma eigenProj_mul_ite {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian)
    : ∀ a b, eigenProj hA a * eigenProj hA b = if a = b then eigenProj hA a else 0 := by
  intro a b
  by_cases hab : a = b
  · simp [hab, eigenProj_idem]
  · simp [hab, eigenProj_orthag]

/--
The eigen projectors of a matrix sum to the identity matrix
-/
lemma eigenProj_sum {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian)
    : ∑ μ ∈ (Set.range hA.eigenvalues).toFinset, eigenProj hA μ = 1 := by
  sorry


/-- **Spectral decomposition of a Hermitian matrix.** A Hermitian matrix `A` is
equal to the sum, over its distinct eigenvalues `μ`, of `μ` times the orthogonal
projector onto the `μ`-eigenspace. -/
theorem isHermitian_spectral_decomposition
    {V : Type} [Fintype V] [DecidableEq V]
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
    /-rw [Matrix.exp_sum_of_commute
        (Finset.image g.adjMatrix_hermitian.eigenvalues Finset.univ)
        f (by sorry)]
    unfold f
    congr
    · skip
    · intro i
      rw [Matrix.exp_nsmul (Complex.I * ↑t * ↑x)]-/
  sorry
  --simp

def K2 : QWalkGraph (Fin 2) :=
  QWalkGraph.of (SimpleGraph.completeGraph (Fin 2))

example : UniformMixing K2 := by
  use (Real.pi / 4)
  unfold UniformMixingAtTimeT QWalkGraph.M
  rw [U_spectral_decomp]
  simp
  have hadj : K2.adjMatrix = !![0, 1; 1, 0] := by
    funext i j
    have hx : i = 0 ∨ i = 1 := by grind
    have hy : j = 0 ∨ j = 1 := by grind
    unfold K2
    unfold QWalkGraph.of
    fin_cases i <;> fin_cases j <;> simp

  let l1 : ℝ := 1
  let u1 : Fin 2 → ℂ := (1 / Real.sqrt 2 : ℂ) • ![1, 1]
  let l2 : ℝ := -1
  let u2 : Fin 2 → ℂ := (1 / Real.sqrt 2 : ℂ) • ![1, -1]

  let eigenvalues : (Fin 2 → ℝ ):= ![l1, l2]
  let eigenvectors : (Fin 2 → (Fin 2 → ℂ)) := ![u1, u2]

  have heigens : ∀ n, K2.adjMatrix.mulVec (eigenvectors n) = (eigenvalues n) • (eigenvectors n) := by
   sorry
  #check K2.adjMatrix_hermitian.eigenvectorBasis
  #check K2.adjMatrix_hermitian.eigenvectorBasis
  sorry
  /-have horth : Orthonormal ℂ ↑eigenvectors := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [heigens]

  have hEigen : K2.adjMatrix_hermitian.eigenvalues = ![1, -1] := by
    ext i
    fin_cases i <;> simp [hadj]
    unfold Matrix.IsHermitian.eigenvalues
    sorry
  unfold eigenProj

  simp
  have K2_symm : (K2.adjMatrix.toEuclideanLin).IsSymmetric := by sorry
    --simpa using K2.adjMatrix_hermitian.isSymmetric_toEuclideanLin
  --#check LinearMap.IsSymmetric.toMatrix_eigenvectorBasis K2_symm
  sorry-/
