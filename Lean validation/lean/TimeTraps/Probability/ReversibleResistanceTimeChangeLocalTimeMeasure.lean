module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeClockIdentities
public import TimeTraps.Probability.ReflectedInteriorOccupationStieltjesIntegral

@[expose] public section

/-! Transport of the actual fixed-level contact measure by the literal
clock. The mapped measure has the increments of the sampled local time
and is carried by physical visits to that same level. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

noncomputable def reversibleResistanceLocalTimeMeasure (A : IntervalMedium) (x a : ℝ)
    (ω : ℕ → ℝ) : Measure ℝ :=
  (reflectedInteriorOccupationTimeMeasure (A.resistance x)
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * 1)) A.resistanceLength_pos
      (A.resistance a) ω).map (fun r => (reversibleResistanceClock A x r.toNNReal ω : ℝ))

theorem reversibleResistanceLocalTimeMeasure_Ioc (A : IntervalMedium) (x a : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (hr : reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a) ω) (S T : ℝ≥0) :
    reversibleResistanceLocalTimeMeasure A x a ω (Ioc S.val T.val) =
      ENNReal.ofReal (reversibleResistanceLocalTime A x a T ω -
        reversibleResistanceLocalTime A x a S ω) := by
  rw [reversibleResistanceLocalTimeMeasure,
    Measure.map_apply (reversibleResistanceClock_real_measurable A x ω) measurableSet_Ioc,
    reversibleResistanceClock_preimage_Ioc A x hω,
    reflectedInteriorOccupationTimeMeasure_eq_stieltjes, StieltjesFunction.measure_Ioc,
    reflectedInteriorOccupationStieltjes_apply_nnreal _ _ hr,
    reflectedInteriorOccupationStieltjes_apply_nnreal _ _ hr]
  rfl

theorem reversibleResistanceLocalTimeMeasure_mass (A : IntervalMedium) (x a : ℝ)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (hr : reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a) ω) (T : ℝ≥0) :
    reversibleResistanceLocalTimeMeasure A x a ω (Ioc (0 : ℝ) T.val) =
      ENNReal.ofReal (reversibleResistanceLocalTime A x a T ω) := by
  have hi := reversibleResistanceLocalTimeMeasure_Ioc A x a hω hr 0 T
  change reversibleResistanceLocalTimeMeasure A x a ω (Ioc (0 : ℝ) T.val) = _ at hi
  have hz : reversibleResistanceLocalTime A x a 0 ω = 0 := by
    rw [reversibleResistanceLocalTime, reversibleResistanceInversePath_zero,
      reflectedInteriorOccupationCoefficient,
      reflectedInteriorCorrection_zero (Real.sqrt_pos.mpr (by norm_num)) hr, zero_div]
  simpa only [hz, sub_zero] using hi

theorem reversibleResistanceLocalTimeMeasure_contact (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω)
    (hr : reflectedInteriorLocalTimeRegular (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a) ω) :
    ∀ᵐ t ∂reversibleResistanceLocalTimeMeasure A x a ω,
      0 ≤ t ∧ reversibleResistancePath A x t.toNNReal ω = a := by
  let q : ℝ → ℝ≥0 × (ℕ → ℝ) := fun t => (t.toNNReal, ω)
  have hq : Measurable q := continuous_real_toNNReal.measurable.prodMk measurable_const
  have hm := (reversibleResistancePath_jointlyMeasurable A x).comp hq
  dsimp only [Function.comp_def, q] at hm
  apply (ae_map_iff (reversibleResistanceClock_real_measurable A x ω).aemeasurable
    ((measurableSet_le measurable_const measurable_id).inter
      (measurableSet_eq_fun hm measurable_const))).mpr
  filter_upwards [(reflectedInteriorOccupationTimeMeasure (A.resistance x)
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * 1)) A.resistanceLength_pos
      (A.resistance a) ω).support_mem_ae] with r hsupport
  have hc := reflectedInteriorOccupationTimeMeasure_support
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * 1)) A.resistanceLength_pos
      (reversibleResistance_site_interior A ha) hr hsupport
  have hY : reversibleResistanceReference A x r.toNNReal ω = A.resistance a := hc.2
  refine ⟨(reversibleResistanceClock A x r.toNNReal ω).coe_nonneg, ?_⟩
  change reversibleResistancePath A x
    (Real.toNNReal (reversibleResistanceClock A x r.toNNReal ω : ℝ)) ω = a
  have hnn := Real.toNNReal_coe (r := reversibleResistanceClock A x r.toNNReal ω)
  calc
    _ = reversibleResistancePath A x (reversibleResistanceClock A x r.toNNReal ω) ω :=
      congrArg (fun t => reversibleResistancePath A x t ω) hnn
    _ = A.resistanceInverse (reversibleResistanceReference A x r.toNNReal ω) :=
      reversibleResistancePath_clock A x hω r.toNNReal
    _ = a := (congrArg A.resistanceInverse hY).trans
      (A.resistanceInverse_resistance (Ioo_subset_Icc_self ha))

end TimeTraps.Probability
