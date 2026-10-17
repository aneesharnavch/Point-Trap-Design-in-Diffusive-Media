module

public import TimeTraps.Probability.ReflectedFiniteKinkC2Formula
public import TimeTraps.Probability.ReflectedFiniteKinkC2IntegrandPath
public import TimeTraps.Probability.ReflectedFoldRegulatorPaths

@[expose] public section

/-! The actual finite-kink reflected formula on one event throughout a
fixed compact horizon. Continuity extends the countable dense-time
identities; the physical occupation normalization is then pointwise. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedFiniteKinkC2_continuous_ae (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath t ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x) =
      reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t ω +
        D * reflectedC2ItoDrift F brownianDyadicPath L D x t ω +
        (∑ i, c i * reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) t ω) +
        finiteKinkSlope F Finset.univ a c 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
        finiteKinkSlope F Finset.univ a c L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω := by
  let V := finiteKinkPotential F Finset.univ a c
  let R (t : ℝ≥0) (ω : ℕ → ℝ) :=
    reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t ω +
      D * reflectedC2ItoDrift F brownianDyadicPath L D x t ω +
      (∑ i, c i * reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) t ω) +
      finiteKinkSlope F Finset.univ a c 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
      finiteKinkSlope F Finset.univ a c L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω
  have ht (t : BrownianCompactTime T) : ∀ᵐ ω ∂brownianDyadicMeasure,
      V (foldedTrajectory L D x brownianDyadicPath t.val ω) - V (reflectedFold L x) = R t.val ω := by
    filter_upwards [reflectedFiniteKinkC2_formula hF L hL D hD a c ha x t.val,
      reflectedFiniteKinkC2HorizonPath_integral_ae hF L hL D hD a c ha x T t.val] with ω hf hi
    rw [min_eq_left t.property.2] at hi
    rw [← hi] at hf
    exact hf
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      V (foldedTrajectory L D x brownianDyadicPath (denseSeq (BrownianCompactTime T) n).val ω) -
        V (reflectedFold L x) = R (denseSeq (BrownianCompactTime T) n).val ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime T) n))
  have hC : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  filter_upwards [hall, hC,
    reflectedC2ItoDrift_continuous_ae hF brownianDyadicPath_isBrownianReal L hL D x,
    reflectedFoldRegulatorPaths_ae x hσ hL] with ω he hc hd hr
  have hleft := ((finiteKinkPotential_continuous hF.continuous Finset.univ a c).comp
    hr.path_continuous).sub (continuous_const (y := V (reflectedFold L x)))
  have hsum : Continuous (fun t => ∑ i, c i *
      reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) t ω) :=
    continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul
      (reflectedInteriorCorrection_continuous hσ hL (hc i)))
  have hright : Continuous (fun t => R t ω) :=
    ((((reflectedFiniteKinkC2HorizonPath_continuous hF L hL D hD a c ha x T ω).add
      (continuous_const.mul hd)).add hsum).add (continuous_const.mul hr.lower_continuous)).sub
        (continuous_const.mul hr.upper_continuous)
  have heq := (denseRange_denseSeq (BrownianCompactTime T)).equalizer
    (hleft.comp continuous_subtype_val) (hright.comp continuous_subtype_val) (funext he)
  exact fun t ht => congrFun heq ⟨t, zero_le, ht⟩

theorem reflectedFiniteKinkC2_occupation_continuous_ae (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath t ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x) =
      reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t ω +
        D * reflectedC2ItoDrift F brownianDyadicPath L D x t ω +
        2 * D * (∑ i, c i * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) t ω) +
        finiteKinkSlope F Finset.univ a c 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
        finiteKinkSlope F Finset.univ a c L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω := by
  filter_upwards [reflectedFiniteKinkC2_continuous_ae hF L hL D hD a c ha x T] with ω hω
  intro t ht
  have hs : (∑ i, c i * reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) t ω) =
      2 * D * ∑ i, c i * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) t ω := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he := reflectedInteriorOccupationCoefficient_normalization x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) L (a i) t ω
    rw [Real.sq_sqrt (by positivity)] at he
    rw [← he]
    ring
  have he := hω t ht
  rw [hs] at he
  exact he

end TimeTraps.Probability
