import QWalkMixing.Support

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
The standard basis vector corresponding to vertex i
-/
@[simp]
abbrev e {V : Type} [DecidableEq V] (i : V) : V → ℂ := Pi.single i 1
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
  rw [two_mul]
  exact hPST_self
