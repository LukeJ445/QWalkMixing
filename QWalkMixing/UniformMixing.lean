import QWalkMixing.Support

theorem UniformMixing_switchingEquivalence {V : Type} [Fintype V] [DecidableEq V]
    {t : ℝ} {g h : QWalkGraph V} (hmix : UniformMixingAtTimeT g t)
    (hequiv : g.switchingEquivalent h) : UniformMixingAtTimeT h t := by
  sorry
