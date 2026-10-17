module

public import TimeTraps.Probability.ContinuousPathLocalTimeData

@[expose] public section

/-! Uniform band convergence on every natural time horizon gives a
single compact-open continuous-path limit. This turns countably many
compact-horizon estimates into the canonical good-path condition. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

theorem continuousPath_tendsto_of_natural_sup {F : ℕ → ReversibleNeumannFullPath}
    {l : ReversibleNeumannFullPath}
    (h : ∀ N : ℕ, Tendsto (fun n => ⨆ t : BrownianCompactTime (N : ℝ≥0),
      |F n t.val - l t.val|) atTop (𝓝 0)) : Tendsto F atTop (𝓝 l) := by
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge b
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(h N).eventually (Iio_mem_nhds hε)] with n hn
  intro t ht
  let u : BrownianCompactTime (N : ℝ≥0) := ⟨t, zero_le, (hb ht).trans hN⟩
  let e : C(BrownianCompactTime (N : ℝ≥0), ℝ) :=
    ⟨fun r => F n r.val - l r.val,
      ((F n).continuous.comp continuous_subtype_val).sub (l.continuous.comp continuous_subtype_val)⟩
  have he : ‖e‖ = ⨆ r : BrownianCompactTime (N : ℝ≥0), |F n r.val - l r.val| := by
    simpa only [e, ContinuousMap.coe_mk, Real.norm_eq_abs] using e.norm_eq_iSup_norm
  have hbnd : |F n t - l t| ≤ ‖e‖ := e.norm_coe_le_norm u
  rw [Real.dist_eq, abs_sub_comm]
  exact hbnd.trans_lt (he.trans_lt hn)

theorem hasContinuousOccupationLocalTime_of_natural_sup (a : ℝ) (m : ℝ → ℝ)
    (p l : ReversibleNeumannFullPath)
    (h : ∀ N : ℕ, Tendsto (fun r : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
      |continuousPathOccupationBand a r (m r) p t.val - l t.val|) (𝓝[>] 0) (𝓝 0)) :
    HasContinuousOccupationLocalTime a m p ∧ continuousPathLocalTime a m p = l := by
  have hl : Tendsto (fun n => continuousPathOccupationBand a (occupationBandRadius n)
      (m (occupationBandRadius n)) p) atTop (𝓝 l) :=
    continuousPath_tendsto_of_natural_sup (fun N => (h N).comp occupationBandRadius_tendsto)
  exact ⟨⟨l, hl⟩, continuousPathLocalTime_eq_of_tendsto a m p l hl⟩

end TimeTraps.Probability

end
