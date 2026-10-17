module

public import TimeTraps.Probability.ReflectedFiniteKinkC2Coefficient
public import TimeTraps.Probability.ReflectedInteriorOccupationMoments

@[expose] public section

/-! Square integrability of finite-kink potential values and of their
actual interior correction sums. Values are bounded on the compact
folded range; no global potential bound is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedFiniteKinkC2_value_memLp (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (a c : ι → ℝ) (T : ℝ≥0) :
    MemLp (fun ω => finiteKinkPotential F Finset.univ a c
      (foldedTrajectory L D x brownianDyadicPath T ω)) 2 brownianDyadicMeasure := by
  have hc := finiteKinkPotential_continuous hF.continuous Finset.univ a c
  let V : C(Icc (0 : ℝ) L, ℝ) := ⟨fun y => finiteKinkPotential F Finset.univ a c y.val,
    hc.comp continuous_subtype_val⟩
  have hm := hc.measurable.comp
    (foldedTrajectory_measurable L D x brownianDyadicPath brownianDyadicPath_measurable T)
  apply MemLp.of_bound hm.aestronglyMeasurable ‖V‖
  exact Eventually.of_forall (fun ω => V.norm_coe_le_norm
    ⟨foldedTrajectory L D x brownianDyadicPath T ω,
      foldedTrajectory_mem L hL D x brownianDyadicPath T ω⟩)

theorem reflectedFiniteKinkC2_value_difference_memLp (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (a c : ι → ℝ) (T : ℝ≥0) :
    MemLp (fun ω => finiteKinkPotential F Finset.univ a c
      (foldedTrajectory L D x brownianDyadicPath T ω) -
      finiteKinkPotential F Finset.univ a c (reflectedFold L x)) 2 brownianDyadicMeasure :=
  (reflectedFiniteKinkC2_value_memLp hF L hL D x a c T).sub (memLp_const _)

theorem reflectedFiniteKinkC2_correction_sum_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a c : ι → ℝ) (T : ℝ≥0) :
    MemLp (fun ω => ∑ i, c i * reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω)
      2 brownianDyadicMeasure :=
  memLp_finsetSum Finset.univ (fun i _ =>
    (reflectedInteriorCorrection_memLp L hL D hD x (a i) T).const_mul (c i))

theorem reflectedFiniteKinkC2_occupation_sum_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a c : ι → ℝ) (T : ℝ≥0) :
    MemLp (fun ω => ∑ i, c i *
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω)
      2 brownianDyadicMeasure :=
  memLp_finsetSum Finset.univ (fun i _ =>
    (reflectedInteriorOccupationCoefficient_memLp L hL D hD x (a i) T).const_mul (c i))

end TimeTraps.Probability
