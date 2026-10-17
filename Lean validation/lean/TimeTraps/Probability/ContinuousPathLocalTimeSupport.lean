module

public import TimeTraps.Probability.ContinuousPathLocalTimeCocycle
public import TimeTraps.Analysis.StieltjesLocalSupport

@[expose] public section

/-! Contact support is derived directly from the shrinking bands. On a
closed time interval avoiding the site, sufficiently narrow bands have
zero increment. Their canonical limit is locally constant away from the
site, so its atomless Stieltjes measure is carried by contact times. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem continuousPathOccupationBand_eq_of_separated (a h m : ℝ)
    (p : ReversibleNeumannFullPath) (s t : ℝ≥0) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, h ≤ |p r - a|) :
    continuousPathOccupationBand a h m p t = continuousPathOccupationBand a h m p s := by
  have hz : (∫ r in s.val..t.val, brownianBandIndicator a h (p r.toNNReal)) = 0 := by
    calc
      _ = ∫ _r in s.val..t.val, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' := uIcc_of_le (show s.val ≤ t.val from hst) ▸ hr
        have hrs : s ≤ r.toNNReal := by
          apply NNReal.coe_le_coe.mp
          rw [Real.coe_toNNReal r (s.property.trans hr'.1)]
          exact hr'.1
        change brownianBandIndicator a h (p r.toNNReal) = 0
        rw [brownianBandIndicator_apply, if_neg (not_lt.mpr
          (hp r.toNNReal ⟨hrs, Real.toNNReal_le_iff_le_coe.mpr hr'.2⟩))]
      _ = 0 := by simp
  have he := intervalIntegral.integral_add_adjacent_intervals
    (continuousPathBand_intervalIntegrable p a h 0 s.val)
    (continuousPathBand_intervalIntegrable p a h s.val t.val)
  rw [hz, add_zero] at he
  exact congrArg (fun z : ℝ => z / m) he.symm

theorem HasContinuousOccupationLocalTime.eq_of_avoids {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p)
    (s t : ℝ≥0) (hst : s ≤ t) (hp : ∀ r ∈ Icc s t, p r ≠ a) :
    continuousPathLocalTime a m p t = continuousPathLocalTime a m p s := by
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hst)
    ((p.continuous.sub continuous_const).abs.continuousOn)
  have heps : 0 < |p u - a| := abs_pos.mpr (sub_ne_zero.mpr (hp u hu))
  have hn : ∀ᶠ n in atTop, occupationBandRadius n < |p u - a| :=
    occupationBandRadius_tendsto.eventually
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds heps))
  have he : (fun n => continuousPathOccupationBand a (occupationBandRadius n)
      (m (occupationBandRadius n)) p t) =ᶠ[atTop]
      (fun n => continuousPathOccupationBand a (occupationBandRadius n)
        (m (occupationBandRadius n)) p s) := by
    filter_upwards [hn] with n hn
    exact continuousPathOccupationBand_eq_of_separated a (occupationBandRadius n)
      (m (occupationBandRadius n)) p s t hst (fun r hr => hn.le.trans (hmin hr))
  exact tendsto_nhds_unique (h.eval_tendsto t) ((h.eval_tendsto s).congr' he.symm)

theorem HasContinuousOccupationLocalTime.locally_constant {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p)
    (t : ℝ≥0) (ht : p t ≠ a) :
    ∀ᶠ r in 𝓝 t, continuousPathLocalTime a m p r = continuousPathLocalTime a m p t := by
  have hn : {r | p r ≠ a} ∈ 𝓝 t :=
    ((isClosed_singleton.preimage p.continuous).isOpen_compl).mem_nhds ht
  obtain ⟨s, u, htu, hN, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hn
  filter_upwards [hN] with r hr
  rcases le_total r t with hrt | htr
  · exact (h.eq_of_avoids r t hrt
      (fun z hz => hsub ⟨hr.1.trans hz.1, hz.2.trans htu.2⟩)).symm
  · exact h.eq_of_avoids t r htr
      (fun z hz => hsub ⟨htu.1.trans hz.1, hz.2.trans hr.2⟩)

def continuousPathLocalTimeMeasure {a : ℝ} {m : ℝ → ℝ} {p : ReversibleNeumannFullPath}
    (h : HasContinuousOccupationLocalTime a m p) (hm : ∀ r, 0 < r → 0 ≤ m r) : Measure ℝ :=
  (continuousStieltjesFunction (fun t => continuousPathLocalTime a m p t.toNNReal)
    ((h.monotone hm).comp Real.toNNReal_monotone)
    ((continuousPathLocalTime a m p).continuous.comp continuous_real_toNNReal)).measure

theorem continuousPathLocalTimeMeasure_Ioc {a : ℝ} {m : ℝ → ℝ} {p : ReversibleNeumannFullPath}
    (h : HasContinuousOccupationLocalTime a m p) (hm : ∀ r, 0 < r → 0 ≤ m r) (s t : ℝ≥0) :
    continuousPathLocalTimeMeasure h hm (Ioc s.val t.val) =
      ENNReal.ofReal (continuousPathLocalTime a m p t - continuousPathLocalTime a m p s) := by
  rw [continuousPathLocalTimeMeasure, StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (continuousPathLocalTime a m p t.val.toNNReal -
    continuousPathLocalTime a m p s.val.toNNReal) = _
  exact congrArg ENNReal.ofReal (congrArg₂ (fun u v : ℝ => u - v)
    (congrArg (continuousPathLocalTime a m p) (show t.val.toNNReal = t from Real.toNNReal_coe))
    (congrArg (continuousPathLocalTime a m p) (show s.val.toNNReal = s from Real.toNNReal_coe)))

theorem continuousPathLocalTimeMeasure_singleton {a : ℝ} {m : ℝ → ℝ} {p : ReversibleNeumannFullPath}
    (h : HasContinuousOccupationLocalTime a m p) (hm : ∀ r, 0 < r → 0 ≤ m r) (t : ℝ) :
    continuousPathLocalTimeMeasure h hm {t} = 0 :=
  continuousStieltjesFunction_measure_singleton _ _ _ t

theorem continuousPathLocalTimeMeasure_support {a : ℝ} {m : ℝ → ℝ} {p : ReversibleNeumannFullPath}
    (h : HasContinuousOccupationLocalTime a m p) (hm : ∀ r, 0 < r → 0 ≤ m r) :
    (continuousPathLocalTimeMeasure h hm).support ⊆ {t : ℝ | 0 ≤ t ∧ p t.toNNReal = a} := by
  intro t ht
  have ht0 : 0 ≤ t := by
    by_contra hn
    have hn' : t < 0 := lt_of_not_ge hn
    have hf : ∀ᶠ r in 𝓝 t, continuousPathLocalTime a m p r.toNNReal =
        continuousPathLocalTime a m p t.toNNReal := by
      filter_upwards [Iio_mem_nhds hn'] with r hr
      rw [Real.toNNReal_of_nonpos (show r ≤ 0 from (show r < 0 from hr).le),
        Real.toNNReal_of_nonpos hn'.le]
    exact (continuousStieltjesFunction_notMem_support _ _ _ t hf) ht
  refine ⟨ht0, ?_⟩
  by_contra hn
  have hf := continuous_real_toNNReal.continuousAt.tendsto.eventually (h.locally_constant t.toNNReal hn)
  exact (continuousStieltjesFunction_notMem_support _ _ _ t hf) ht

end TimeTraps.Probability

end
