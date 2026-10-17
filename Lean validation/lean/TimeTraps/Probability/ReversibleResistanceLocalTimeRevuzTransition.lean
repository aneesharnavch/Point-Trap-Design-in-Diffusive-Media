module

public import TimeTraps.Probability.ReversibleResistanceTransitionRegularity

@[expose] public section

/-! Compact-time joint measurability of the actual transition for arbitrary
Borel tests, including discontinuous band indicators. This uses the genuine
measurable inverse-clock functional on a common compact reference path. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reflectedMarkovPathTimeChange_jointlyMeasurable (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y) :
    Measurable (fun q : ℝ≥0 × ReflectedMarkovPath L H =>
      reflectedMarkovPathTimeChange L hL H c hc hpos q.1 q.2) :=
  (reflectedMarkovPathExtend_joint_continuous L H).measurable.comp
    ((reflectedMarkovPathSpeed_inverse_measurable L hL H c hc hpos).prodMk measurable_snd)

theorem reflectedTimeChangedOperator_compact_jointlyMeasurable_borel
    (L : ℝ) (hL : 0 < L) (D : ℝ) (T H : ℝ≥0) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y) (hH : T / m ≤ H)
    {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun q : BrownianCompactTime T × Icc (0 : ℝ) L =>
      reflectedTimeChangedOperator L D c q.1.val f q.2.val) := by
  let G : ℝ≥0 × ReflectedMarkovPath L H → ℝ := fun q =>
    f (reflectedMarkovPathTimeChange L hL H (fun y : Icc (0 : ℝ) L => c y.val)
      hc.domRestrict (fun y => hpos y.val y.property) q.1 q.2).val
  have hG : Measurable G := hf.comp (measurable_subtype_coe.comp
    (reflectedMarkovPathTimeChange_jointlyMeasurable L hL H _ hc.domRestrict _))
  let Φ : (BrownianCompactTime T × Icc (0 : ℝ) L) × BrownianCompletedSample → ℝ := fun q =>
    G (q.1.1.val, reflectedMarkovFreshPath L hL D H (q.1.2, q.2))
  have hΦ : Measurable Φ := hG.comp
    ((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
      ((reflectedMarkovFreshPath_measurable L hL D H).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hi : Measurable (fun q => ∫ ω, Φ (q, ω) ∂brownianCompletedMeasure) :=
    hΦ.stronglyMeasurable.integral_prod_right'.measurable
  have he : (fun q : BrownianCompactTime T × Icc (0 : ℝ) L =>
      reflectedTimeChangedOperator L D c q.1.val f q.2.val) =
      (fun q => ∫ ω, Φ (q, ω) ∂brownianCompletedMeasure) := by
    funext q
    exact (reflectedTimeChangedOperator_path L hL D H c hc hpos m hm hmc q.1.val
      ((div_le_div_of_nonneg_right q.1.property.2 (zero_le : (0 : ℝ≥0) ≤ m)).trans hH) f q.2).symm
  exact he.symm ▸ hi

theorem reversibleResistanceTransition_compact_jointlyMeasurable_borel (A : IntervalMedium) (T : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun q : BrownianCompactTime T × Icc A.source.left A.source.right =>
      reversibleResistanceTransition A q.1.val f q.2.val) := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) A.resistanceLength).Nonempty from ⟨0, le_rfl, A.resistanceLength_pos.le⟩)
      A.resistanceSpeed_continuous.continuousOn
  let m : ℝ≥0 := ⟨A.resistanceSpeed y, (A.resistanceSpeed_pos y).le⟩
  let R : Icc A.source.left A.source.right → Icc (0 : ℝ) A.resistanceLength :=
    fun x => ⟨A.resistance x.val, A.resistance_mem x.property⟩
  have hR : Measurable R := A.resistance_continuous.domRestrict.measurable.subtype_mk
  have hm := (reflectedTimeChangedOperator_compact_jointlyMeasurable_borel A.resistanceLength
    A.resistanceLength_pos 1 T (T / m) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun z _ => A.resistanceSpeed_pos z) m (A.resistanceSpeed_pos y) (fun z hz => hmin hz) le_rfl
        (hf.comp A.resistanceInverse_continuous.measurable)).comp
          (measurable_fst.prodMk (hR.comp measurable_snd))
  have he : (fun q : BrownianCompactTime T × Icc A.source.left A.source.right =>
      reversibleResistanceTransition A q.1.val f q.2.val) =
      (fun q => reflectedTimeChangedOperator A.resistanceLength 1 A.resistanceSpeed q.1.val
        (f ∘ A.resistanceInverse) (R q.2).val) := by
    funext q
    exact reversibleResistanceTransition_reference A q.1.val f q.2.val
  exact he.symm ▸ hm

end TimeTraps.Probability

end
