module

public import TimeTraps.Probability.ReflectedLocalTimeBandData
public import TimeTraps.Probability.ReversibleResistanceTimeChangeSubstitution
public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeData

@[expose] public section

/-! Genuine bands of the physical particle path, in resistance coordinates,
with reciprocal speed weight. The extension of the state test outside the
physical interval is by projection and has no effect on the actual path. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def reversibleResistanceBandTest (A : IntervalMedium) (a h z : ℝ) : ℝ :=
  let p := projIcc A.source.left A.source.right A.source.increasing.le z
  brownianBandIndicator (A.resistance a) h (A.resistance p) /
    (A.conductance p * A.source.density p)

theorem reversibleResistanceBandTest_measurable (A : IntervalMedium) (a h : ℝ) :
    Measurable (reversibleResistanceBandTest A a h) := by
  let p : ℝ → ℝ := fun z => (projIcc A.source.left A.source.right A.source.increasing.le z : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpI : ∀ z, p z ∈ Icc A.source.left A.source.right := fun z =>
    (projIcc A.source.left A.source.right A.source.increasing.le z).property
  exact ((brownianBandIndicator_measurable (A.resistance a) h).comp
    (A.resistance_continuous.comp_continuous hp hpI).measurable).div
      ((A.conductance_continuous.mul A.source.continuous).comp_continuous hp hpI).measurable

theorem reversibleResistanceBandTest_eq (A : IntervalMedium) (a h : ℝ) {z : ℝ}
    (hz : z ∈ Icc A.source.left A.source.right) :
    reversibleResistanceBandTest A a h z = brownianBandIndicator (A.resistance a) h (A.resistance z) /
      (A.conductance z * A.source.density z) := by
  simp only [reversibleResistanceBandTest, projIcc_of_mem A.source.increasing.le hz]

noncomputable def reversibleResistanceOccupationBand (A : IntervalMedium) (x a h : ℝ)
    (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  (1 / (2 * h)) * brownianItoDrift (reversibleResistancePath A x) (reversibleResistanceBandTest A a h) T ω

theorem reversibleResistanceOccupationBand_formula (A : IntervalMedium) (x a h : ℝ)
    (T : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistanceOccupationBand A x a h T ω = (1 / (2 * h)) *
      ∫ t in (0 : ℝ)..T.val,
        (if |A.resistance (reversibleResistancePath A x t.toNNReal ω) - A.resistance a| < h then (1 : ℝ) else 0) /
          (A.conductance (reversibleResistancePath A x t.toNNReal ω) *
            A.source.density (reversibleResistancePath A x t.toNNReal ω)) := by
  simp only [reversibleResistanceOccupationBand, brownianItoDrift,
    reversibleResistanceBandTest_eq A a h (reversibleResistancePath_mem A x _ ω), brownianBandIndicator_apply]

theorem reversibleResistanceOccupationBand_measurable (A : IntervalMedium) (x a h : ℝ) (T : ℝ≥0) :
    Measurable (reversibleResistanceOccupationBand A x a h T) :=
  measurable_const.mul (brownianItoDrift_bounded_measurable
    (reversibleResistanceBandTest_measurable A a h) (reversibleResistancePath_jointlyMeasurable A x) T)

theorem reversibleResistanceOccupationBand_reference_ae (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (a h : ℝ) (T : ℝ≥0),
      reversibleResistanceOccupationBand A x a h T ω =
        reflectedOccupationBand A.resistanceLength 1 (A.resistance x) (A.resistance a) h
          (reversibleResistanceInversePath A x T ω) ω := by
  filter_upwards [reversibleResistancePath_integral_reciprocal A x] with ω hω a h T
  have he := hω (fun z => brownianBandIndicator (A.resistance a) h (A.resistance z)) T
  simp only [A.resistance_inverse (reversibleResistanceReference_mem A x _ ω)] at he
  unfold reversibleResistanceOccupationBand reflectedOccupationBand brownianBandOccupation brownianItoDrift
  simp only [reversibleResistanceBandTest_eq A a h (reversibleResistancePath_mem A x _ ω)]
  exact congrArg (fun r : ℝ => (1 / (2 * h)) * r) he.symm

theorem reversibleResistanceInversePath_measurable (A : IntervalMedium) (x : ℝ) (T : ℝ≥0) :
    Measurable (reversibleResistanceInversePath A x T) :=
  reflectedPositiveTimeInversePath_measurable A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) T

theorem reversibleResistanceInversePath_bounded (A : IntervalMedium) (x : ℝ) (T : ℝ≥0) :
    ∃ S : ℝ≥0, ∀ ω, reversibleResistanceInversePath A x T ω ≤ S := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) A.resistanceLength).Nonempty from ⟨0, le_rfl, A.resistanceLength_pos.le⟩)
      A.resistanceSpeed_continuous.continuousOn
  let m : ℝ≥0 := ⟨A.resistanceSpeed y, (A.resistanceSpeed_pos y).le⟩
  refine ⟨T / m, ?_⟩
  exact reflectedPositiveTimeInversePath_bound A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun z _ => A.resistanceSpeed_pos z) m (A.resistanceSpeed_pos y) (fun z hz => hmin hz) T

end TimeTraps.Probability
