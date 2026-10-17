module

public import TimeTraps.Probability.ReflectedGaussianOpenInterval
public import TimeTraps.Probability.ReflectedBrownianTransition
public import TimeTraps.Probability.BrownianStepIntegralIncrement

@[expose] public section

/-! A positive-probability crossing of every interior level between
reference times one and two, from every starting location. A rectangle
of two independent Gaussian variables lies inside the crossing event. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem affineBrownian_pair_interval_pos (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    0 < brownianDyadicMeasure
      {ω | affineBrownianInput x σ 1 ω ∈ Ioo a b ∧
        σ * (brownianDyadicPath 2 ω - brownianDyadicPath 1 ω) ∈ Ioo c d} := by
  let U := affineBrownianInput x σ 1
  let V := fun ω => σ * (brownianDyadicPath 2 ω - brownianDyadicPath 1 ω)
  have hU : StronglyMeasurable[brownianNaturalFiltration brownianDyadicPath
      brownianDyadicPath_measurable 1] U := by
    exact (measurable_const.add (measurable_const.mul
      (brownianNaturalFiltration_stronglyAdapted brownianDyadicPath
        brownianDyadicPath_measurable 1).measurable)).stronglyMeasurable
  have hind : IndepFun U V brownianDyadicMeasure := by
    have h := (brownian_adapted_indep_increment brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable (s := 1) (t := 2) (by norm_num) hU).comp
        (φ := id) (ψ := fun z : ℝ => σ * z)
        measurable_id (measurable_const.mul measurable_id)
    exact h
  have hUL : HasLaw U (gaussianReal x (affineBrownianVariance σ 1)) brownianDyadicMeasure :=
    affineBrownianInput_hasLaw x σ 1
  have hVL : HasLaw V (gaussianReal 0 (affineBrownianVariance σ 1)) brownianDyadicMeasure := by
    have ht : (2 : ℝ≥0) - 1 = 1 := by
      apply NNReal.eq
      rw [NNReal.coe_sub (by norm_num : (1 : ℝ≥0) ≤ 2)]
      norm_num
    simpa only [V, ht] using brownian_scaled_increment_hasLaw brownianDyadicPath_isPreBrownianReal σ
      (s := 1) (t := 2) (by norm_num)
  have hv : affineBrownianVariance σ 1 ≠ 0 :=
    (affineBrownianVariance_pos hσ (by norm_num : (0 : ℝ≥0) < 1)).ne'
  have hu : 0 < brownianDyadicMeasure (U ⁻¹' Ioo a b) := by
    change 0 < brownianDyadicMeasure {ω | U ω ∈ Ioo a b}
    rw [hUL.measure_eq (p := fun y => y ∈ Ioo a b) measurableSet_Ioo]
    exact gaussianReal_Ioo_pos x hv hab
  have hvv : 0 < brownianDyadicMeasure (V ⁻¹' Ioo c d) := by
    change 0 < brownianDyadicMeasure {ω | V ω ∈ Ioo c d}
    rw [hVL.measure_eq (p := fun y => y ∈ Ioo c d) measurableSet_Ioo]
    exact gaussianReal_Ioo_pos 0 hv hcd
  change 0 < brownianDyadicMeasure (U ⁻¹' Ioo a b ∩ V ⁻¹' Ioo c d)
  rw [hind.measure_inter_preimage_eq_mul _ _ measurableSet_Ioo measurableSet_Ioo]
  exact ENNReal.mul_pos hu.ne' hvv.ne'

theorem foldedTrajectory_crossing_probability_pos (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {a : ℝ} (ha : a ∈ Ioo 0 L) :
    0 < brownianDyadicMeasure {ω |
      foldedTrajectory L D x brownianDyadicPath 1 ω < a ∧
      a < foldedTrajectory L D x brownianDyadicPath 2 ω} := by
  let δ := min a (L-a) / 4
  have hδ : 0 < δ := div_pos (lt_min ha.1 (sub_pos.mpr ha.2)) (by norm_num)
  have hδa : 4 * δ ≤ a := by dsimp only [δ]; linarith [min_le_left a (L-a)]
  have hδL : 4 * δ ≤ L-a := by dsimp only [δ]; linarith [min_le_right a (L-a)]
  have hp := affineBrownian_pair_interval_pos x (σ := Real.sqrt (2*D))
    (Real.sqrt_pos.mpr (mul_pos (by norm_num) hD))
      (a := a-δ) (b := a) (c := 2*δ) (d := 3*δ) (by linarith) (by linarith)
  apply hp.trans_le
  apply measure_mono
  intro ω hω
  rcases hω with ⟨h₁,h₂⟩
  let u := affineBrownianInput x (Real.sqrt (2*D)) 1 ω
  let v := Real.sqrt (2*D) * (brownianDyadicPath 2 ω - brownianDyadicPath 1 ω)
  change a-δ < u ∧ u < a at h₁
  change 2*δ < v ∧ v < 3*δ at h₂
  have hu : u ∈ Icc 0 L := ⟨by linarith, by linarith [ha.2]⟩
  have huv : u+v ∈ Icc 0 L := ⟨by linarith [ha.1], by linarith⟩
  have he : x + Real.sqrt (2*D) * brownianDyadicPath 2 ω = u+v := by
    dsimp [u,v,affineBrownianInput]
    ring
  change reflectedFold L u < a ∧ a < reflectedFold L
    (x + Real.sqrt (2*D) * brownianDyadicPath 2 ω)
  rw [he, reflectedFold_eq_self L hL u hu, reflectedFold_eq_self L hL (u+v) huv]
  exact ⟨h₁.2, by linarith⟩

end TimeTraps.Probability
