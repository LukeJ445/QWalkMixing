import QWalkMixing.Definitions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Analysis.SpecialFunctions.Exponential

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

/-
SPECTRAL THEORY
-/

/--
If we have a diagonalization of A, A = ZDZ*, then we can reformulate
A as a sum over the values in D and the outer product of columns of Z
-/
lemma diagonalization_to_eigen_sum {V : Type} [Fintype V] [DecidableEq V]
    {A Z : Matrix V V ℂ} {D : V → ℂ}
    (hA : A = Z * (Matrix.diagonal D) * Z.conjTranspose) :
    A = ∑ μ, D μ • Matrix.vecMulVec (Z.col μ) (star (Z.col μ)) := by
  ext j k
  have rhs_eq : (∑ i, D i • Matrix.vecMulVec (Z.col i) (star (Z.col i))) j k
      = ∑ i, D i * (Z j i) * (star (Z k i)) := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, RCLike.star_def]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Matrix.vecMulVec_apply]
    simp only [Matrix.col_apply, Pi.star_apply, RCLike.star_def]
    ring
  rw [rhs_eq]
  have h_entry : A j k = ∑ i,
      (Z : Matrix V V ℂ) j i *
        (D i : ℂ) *
        star ((Z : Matrix V V ℂ) k i) := by
    conv_lhs => rw [hA]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    -- The inner sum collapses: only the diagonal term at index `i` survives.
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp only [mul_ite, mul_zero, ite_eq_right_iff]
      intro h
      contradiction
    · intro h
      contradiction
  rw [h_entry]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma exp_mem_unitary_conj {V : Type} [Fintype V] [DecidableEq V]
    {A U : Matrix V V ℂ} (hU : U ∈ Matrix.unitaryGroup V ℂ) :
    NormedSpace.exp (U * A * U.conjTranspose) = U * NormedSpace.exp (A) * U.conjTranspose := by
  let Uu : (Matrix V V ℂ)ˣ := ⟨U, star U, Matrix.mem_unitaryGroup_iff.mp hU,
      Matrix.mem_unitaryGroup_iff'.mp hU⟩
  let Uug : Matrix.unitaryGroup V ℂ := ⟨U, hU⟩
  have hU1 : U = ↑Uu := by rfl
  have hU1' : U = ↑Uug := by rfl
  have : star U = ↑Uu⁻¹ := by
    rw [hU1']
    rw [←Matrix.UnitaryGroup.inv_val Uug]
    norm_cast
  rw [←Matrix.star_eq_conjTranspose, hU1, this]
  rw [Matrix.exp_units_conj]

/--
If we have diagonalized the adjacency matrix, then we can compute the unitary
by simply computing the exponential of the eigen values in the diagonalization sum
-/
theorem U_spectral_decomp_to_sum {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) (t : ℝ)
    {Z : Matrix V V ℂ} {D : V → ℂ} (hZ : Z ∈ Matrix.unitaryGroup V ℂ)
    (hA : g.adjMatrix = Z * (Matrix.diagonal D) * Z.conjTranspose) :
    g.U t = ∑ μ,
      Complex.exp (Complex.I * D μ * ↑t) • Matrix.vecMulVec (Z.col μ) (star (Z.col μ)) := by
  unfold QWalkGraph.U
  have hA_exp := congrArg (fun M => NormedSpace.exp ((Complex.I * ↑t) • M)) hA
  have : (Complex.I * ↑t) • (Z * Matrix.diagonal D * Z.conjTranspose) =
          Z * ((Complex.I * ↑t) • Matrix.diagonal D) * Z.conjTranspose := by
    simp
  simp only [] at hA_exp
  rw [this] at hA_exp
  rw [exp_mem_unitary_conj hZ] at hA_exp
  have hTmp : (Complex.I * ↑t) • Matrix.diagonal D =
                Matrix.diagonal (fun v => Complex.I * D v * ↑t) := by
    ext i j
    by_cases hij : i = j
    · rw [hij]
      simp
      ring
    · rw [Matrix.diagonal_apply]
      simp [hij]
  rw [hTmp] at hA_exp
  rw [Matrix.exp_diagonal] at hA_exp
  rw [diagonalization_to_eigen_sum hA_exp]
  rw [Complex.exp_eq_exp_ℂ]
  simp

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

/-
The eigen projectors of a matrix sum to the identity matrix
TODO
lemma eigenProj_sum {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian)
    : ∑ μ ∈ (Set.range hA.eigenvalues).toFinset, eigenProj hA μ = 1 := by
  sorry
-/

/--
If we have a diagonalization sum with some function applied,
we can rewrite the sum as a double sum, grouping distinct eigen values
-/
lemma regroup_eigen_sum_distinct {V : Type} [Fintype V]
    {Z : Matrix V V ℂ} {D : V → ℂ} {f : ℂ → ℂ} :
    ∑ μ, f (D μ) • Matrix.vecMulVec (Z.col μ) (star (Z.col μ)) =
  ∑ μ ∈ (Set.range D).toFinset, f μ •
    (∑ i ∈ Finset.univ.filter (fun i => D i = μ), Matrix.vecMulVec (Z.col i) (star (Z.col i))) := by
  have rhs_eq :
      ∑ μ ∈ (Set.range D).toFinset, f μ •
      (∑ i ∈ Finset.univ.filter (fun i => D i = μ),
        Matrix.vecMulVec (Z.col i) (star (Z.col i)))
      = ∑ μ ∈ (Set.range D).toFinset,
      (∑ i ∈ Finset.univ.filter (fun i => D i = μ), f (D i) •
        Matrix.vecMulVec (Z.col i) (star (Z.col i))) := by
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  rw [rhs_eq]
  rw [Finset.sum_fiberwise_of_maps_to
        (t := (Set.range D).toFinset)
        (g := D)
        (by intro i _; rw [Set.mem_toFinset]; exact Set.mem_range_self i)]

/--
If we have a diagonalization sum,
we can rewrite the sum as a double sum, grouping distinct eigen values
-/
lemma regroup_eigen_sum_distinct' {V : Type} [Fintype V]
    {Z : Matrix V V ℂ} {D : V → ℂ} :
    ∑ μ, D μ • Matrix.vecMulVec (Z.col μ) (star (Z.col μ)) =
  ∑ μ ∈ (Set.range D).toFinset, μ • -- i is a distinct eigen value
    (∑ i ∈ Finset.univ.filter (fun i => D i = μ), Matrix.vecMulVec (Z.col i) (star (Z.col i))) :=
  @regroup_eigen_sum_distinct _ _ _ D id

/-- **Spectral decomposition of a Hermitian matrix.** A Hermitian matrix `A` is
equal to the sum, over its distinct eigenvalues `μ`, of `μ` times the orthogonal
projector onto the `μ`-eigenspace. -/
theorem isHermitian_spectral_decomposition
    {V : Type} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} (hA : A.IsHermitian) :
    A = ∑ μ ∈ (Set.range hA.eigenvalues).toFinset, (μ : ℂ) • eigenProj hA μ := by
  have hA_spectral := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hA_spectral
  rw [Matrix.star_eq_conjTranspose] at hA_spectral
  conv_lhs => rw [diagonalization_to_eigen_sum hA_spectral]
  rw [regroup_eigen_sum_distinct']
  have hinj : Set.InjOn Complex.ofReal ↑(Finset.image hA.eigenvalues Finset.univ) := by
    unfold Set.InjOn
    intro x hx y hy
    exact RCLike.ofReal_inj.mp
  simp only [Complex.coe_algebraMap, Set.toFinset_range, Function.comp_apply,
    Matrix.IsHermitian.eigenvectorUnitary_col_eq, Complex.coe_smul]
  rw [←Finset.image_image, Finset.sum_image hinj]
  simp only [Complex.ofReal_inj, Complex.coe_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold eigenProj
  rfl

/--
Using the spectral decomposition of A, we can compute the Unitary by simply
applying the exponential to the eigenvalues.
-/
theorem U_spectral_decomp {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) (t : ℝ) :
    g.U t = ∑ μ ∈ (Set.range g.adjMatrix_hermitian.eigenvalues).toFinset,
    NormedSpace.exp (Complex.I * ↑μ * t) • eigenProj g.adjMatrix_hermitian μ := by
  have hA_spectral := g.adjMatrix_hermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hA_spectral
  have hU : ↑g.adjMatrix_hermitian.eigenvectorUnitary ∈ Matrix.unitaryGroup V ℂ:= by
    simp
  conv_lhs => rw [U_spectral_decomp_to_sum g t hU hA_spectral]
  let D := Complex.ofReal ∘ g.adjMatrix_hermitian.eigenvalues
  let f := fun x => Complex.exp (Complex.I * x * ↑t)
  have : ∀μ, Complex.exp (Complex.I * (RCLike.ofReal ∘ g.adjMatrix_hermitian.eigenvalues) μ * ↑t) =
        f (D μ) := by
    intro μ
    unfold D f
    rfl
  conv_lhs =>
    rhs
    intro μ
    rw [this μ]
  rw [@regroup_eigen_sum_distinct _ _ _ D f]
  unfold D f
  simp only [WeightedGraph.adjMatrix.eq_1, Set.toFinset_range, Function.comp_apply,
    WeightedGraph.adjMatrix, Matrix.IsHermitian.eigenvectorUnitary_col_eq]
  have hinj : Set.InjOn Complex.ofReal
            ↑(Finset.image g.adjMatrix_hermitian.eigenvalues Finset.univ) := by
    unfold Set.InjOn
    intro x hx y hy
    exact RCLike.ofReal_inj.mp
  rw [←Finset.image_image]
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Complex.ofReal_inj, implies_true,
    Set.injOn_of_eq_iff_eq, Finset.sum_image]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.exp_eq_exp_ℂ]
  unfold eigenProj
  rfl
