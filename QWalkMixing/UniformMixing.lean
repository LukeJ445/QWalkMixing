import QWalkMixing.Support

/--
The diagonal matrix for switching equivalence is unitary
-/
lemma switching_matrix_unitary {V : Type} [Fintype V] [DecidableEq V] {x : V → ℂ}
    (hx : ∀ i, ‖x i‖ = 1) : (Matrix.diagonal x) ∈ Matrix.unitaryGroup V ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  by_cases hij : i = j
  · rw [hij]
    simp only [Matrix.diagonal_mul, Matrix.star_apply, Matrix.diagonal_apply_eq, RCLike.star_def,
      Matrix.one_apply_eq]
    rw [mul_comm, ←Complex.normSq_eq_conj_mul_self]
    norm_cast
    specialize hx j
    apply congrArg (fun x => x^2) at hx
    rw [one_pow, Complex.sq_norm] at hx
    exact hx
  · simp only [Matrix.diagonal_mul, Matrix.star_apply]
    have hij' : j ≠ i := by symm; exact hij
    rw [Matrix.diagonal_apply_ne x hij', Matrix.one_apply_ne hij]
    simp

theorem switching_matrix_U {V : Type} [Fintype V] [DecidableEq V] {g h : QWalkGraph V}
    {x : V → ℂ} (hx : ∀ i, ‖x i‖ = 1)
    (hSeq : (Matrix.diagonal x) * g.adjMatrix * (Matrix.diagonal x).conjTranspose = h.adjMatrix)
    (t : ℝ) : h.U t = (Matrix.diagonal x) * (g.U t) * (Matrix.diagonal x).conjTranspose := by
  unfold QWalkGraph.U
  rw [←hSeq]
  have : (Complex.I * ↑t) • ((Matrix.diagonal x) * g.adjMatrix * (Matrix.diagonal x).conjTranspose)
      = (Matrix.diagonal x) * ((Complex.I * ↑t) • g.adjMatrix) * (Matrix.diagonal x).conjTranspose := by
    simp
  rw [this]
  rw [exp_mem_unitary_conj (switching_matrix_unitary hx)]

theorem UniformMixing_switchingEquivalence {V : Type} [Fintype V] [DecidableEq V]
    {t : ℝ} {g h : QWalkGraph V} (hmix : UniformMixingAtTimeT g t)
    (hequiv : g.switchingEquivalent h) : UniformMixingAtTimeT h t := by
  unfold QWalkGraph.switchingEquivalent at hequiv
  obtain ⟨x, hx1, hx2⟩ := hequiv
  unfold UniformMixingAtTimeT QWalkGraph.M at *
  rw [switching_matrix_U hx1 hx2 t]
  ext i j
  have hx1' : ∀ i, Complex.normSq (x i) = 1 := by
    intro i
    rw [←Complex.sq_norm, sq_eq_one_iff]
    left
    exact hx1 i
  have hmix' := congrArg (fun x => x i j) hmix
  simp only [Matrix.of_apply, Matrix.map_apply, one_div] at hmix'
  simpa [hx1' i, hx1' j]

/--
The QWalkGraph on K2, the complete graph with two vertices.
-/
def K2 : QWalkGraph (Fin 2) :=
  QWalkGraph.of (SimpleGraph.completeGraph (Fin 2))

example : UniformMixing K2 := by
  let t := (Real.pi / 4)
  use t
  unfold UniformMixingAtTimeT QWalkGraph.M
  simp only [Fintype.card_fin, Nat.cast_ofNat, one_div]
  have hadj : K2.adjMatrix = !![0, 1; 1, 0] := by
    funext i j
    unfold K2 QWalkGraph.of
    fin_cases i <;> fin_cases j <;> simp
  let V : Type := Fin 2
  let Z : Matrix (Fin 2) (Fin 2) ℂ := (1 / Real.sqrt 2) • !![1, 1; 1, -1]
  let D : (Fin 2) → ℂ := ![1, -1]
  have hZConjTranspose : Z.conjTranspose = Z := by
    ext i j
    unfold Matrix.conjTranspose
    simp only [RCLike.star_def, Matrix.map_apply, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> norm_num [Z]
  have hDMatrix : Matrix.diagonal D = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [D]
  have hSqrt1 : (↑√2)⁻¹ * (↑√2)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [←pow_two]
    norm_cast
    simp
  have hZ : Z ∈ Matrix.unitaryGroup V ℂ := by
    rw [Matrix.mem_unitaryGroup_iff,
        Matrix.star_eq_conjTranspose, hZConjTranspose]
    unfold Z
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, hSqrt1]
  have hK2 : K2.adjMatrix = Z * (Matrix.diagonal D) * Z.conjTranspose := by
    rw [hadj, hZConjTranspose, hDMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Z, hSqrt1]
  rw [U_spectral_decomp_to_sum K2 t hZ hK2]
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, mul_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_neg, neg_mul, D]
  have hexp1 : Complex.exp (-(Complex.I * t)) = 1 / Real.sqrt 2 * (1 - Complex.I) := by
    rw [←mul_neg, mul_comm, Complex.exp_mul_I]
    unfold t
    norm_cast
    simp
    grind
  have hexp2 : Complex.exp (Complex.I * t) = 1 / Real.sqrt 2 * (1 + Complex.I) := by
    rw [mul_comm, Complex.exp_mul_I]
    unfold t
    norm_cast
    simp
    grind
  rw [hexp1, hexp2]
  have hZ0 : Z.col 0 = ![(↑√2)⁻¹, (↑√2)⁻¹] := by
    unfold Z
    ext i
    fin_cases i <;> norm_num
  have hZ1 : Z.col 1 = ![(↑√2)⁻¹, -(↑√2)⁻¹] := by
    unfold Z
    ext i
    fin_cases i <;> norm_num
  rw [mul_smul, mul_smul, ←smul_add]
  rw [sub_smul, add_smul]
  simp only [one_smul]
  have E0 : Matrix.vecMulVec (Z.col 0) (star (Z.col 0)) = ((1 : ℝ) / 2) • !![1, 1; 1, 1] := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [hZ0, hSqrt1]
  have E1 : Matrix.vecMulVec (Z.col 1) (star (Z.col 1)) = ((1 : ℝ) / 2)  • !![1, -1; -1, 1] := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [hZ1, hSqrt1]
  rw [E0, E1]
  have hHavles: (2 : ℝ)⁻¹ + 2⁻¹ = 1 := by grind
  have hSqrt: √2/2 * (√2/2) = 2⁻¹ := by grind
  funext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.normSq, hHavles, hSqrt]
