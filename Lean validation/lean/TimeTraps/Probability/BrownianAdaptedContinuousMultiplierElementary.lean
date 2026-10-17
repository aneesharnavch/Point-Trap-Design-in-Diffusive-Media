module

public import TimeTraps.Probability.BrownianAdaptedContinuousMultiplierAmbient

@[expose] public section

/-! Multiplication of actual elementary integrands. Intersecting the
time intervals preserves left adaptation; one bounded coefficient and
one L² coefficient give an L² product. Empty intersections are retained
as degenerate elementary intervals. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
variable {hBm : ∀ t, Measurable (B t)} {P : Measure Ω} {M : ℝ≥0}

def BrownianIntegralElementary.boundedProduct (a b : BrownianIntegralElementary B hBm P)
    (ha : ∀ ω, |a.coefficient ω| ≤ M.val) : BrownianIntegralElementary B hBm P where
  left := max a.left b.left
  right := max (max a.left b.left) (min a.right b.right)
  ordered := le_max_left _ _
  coefficient := fun ω => a.coefficient ω * b.coefficient ω
  adapted := (a.adapted.mono ((brownianNaturalFiltration B hBm).mono (le_max_left _ _))).mul
    (b.adapted.mono ((brownianNaturalFiltration B hBm).mono (le_max_right _ _)))
  squareIntegrable := by
    apply b.squareIntegrable.of_le_mul (c := M.val)
      (a.coefficient_measurable.aestronglyMeasurable.mul b.squareIntegrable.aestronglyMeasurable)
    filter_upwards [] with ω
    change ‖a.coefficient ω * b.coefficient ω‖ ≤ M.val * ‖b.coefficient ω‖
    rw [norm_mul, Real.norm_eq_abs (a.coefficient ω)]
    exact mul_le_mul_of_nonneg_right (ha ω) (norm_nonneg _)

theorem brownianAdaptedContinuousMultiplier_elementary_process
    (a b : BrownianIntegralElementary B hBm P) (ha : ∀ ω, |a.coefficient ω| ≤ M.val)
    (p : ℝ × Ω) :
    brownianElementaryProcess (a.boundedProduct b ha).left (a.boundedProduct b ha).right
      (a.boundedProduct b ha).coefficient p =
      brownianElementaryProcess a.left a.right a.coefficient p *
        brownianElementaryProcess b.left b.right b.coefficient p := by
  have hi : brownianIntervalIndicator (max a.left b.left)
      (max (max a.left b.left) (min a.right b.right)) p.1 =
      brownianIntervalIndicator (max a.left b.left) (min a.right b.right) p.1 := by
    apply congrArg (fun s : Set ℝ => s.indicator (fun _ => (1 : ℝ)) p.1)
    change Ioc (max a.left.val b.left.val)
      (max (max a.left.val b.left.val) (min a.right.val b.right.val)) =
        Ioc (max a.left.val b.left.val) (min a.right.val b.right.val)
    rw [← Ioc_union_Ioc_right, Ioc_self, empty_union]
  change brownianIntervalIndicator (max a.left b.left)
      (max (max a.left b.left) (min a.right b.right)) p.1 *
      (a.coefficient p.2 * b.coefficient p.2) =
    (brownianIntervalIndicator a.left a.right p.1 * a.coefficient p.2) *
      (brownianIntervalIndicator b.left b.right p.1 * b.coefficient p.2)
  rw [hi, ← brownianIntervalIndicator_mul]
  ring

theorem brownianAdaptedContinuousMultiplier_elementary_bound
    (a : BrownianIntegralElementary B hBm P) (ha : ∀ ω, |a.coefficient ω| ≤ M.val)
    (p : ℝ × Ω) : |brownianElementaryProcess a.left a.right a.coefficient p| ≤ M.val := by
  change |(Ioc a.left.val a.right.val).indicator (fun _ => 1) p.1 * a.coefficient p.2| ≤ M.val
  by_cases hp : p.1 ∈ Ioc a.left.val a.right.val
  · simpa only [Set.indicator_of_mem hp, one_mul] using ha p.2
  · simpa only [Set.indicator_of_notMem hp, zero_mul, abs_zero] using M.property

theorem brownianAdaptedContinuousMultiplier_elementary
    (a b : BrownianIntegralElementary B hBm P) (ha : ∀ ω, |a.coefficient ω| ≤ M.val) :
    brownianAdaptedContinuousMultiplierAmbient
      (brownianElementaryProcess_measurable a.left a.right a.coefficient_measurable)
      (brownianAdaptedContinuousMultiplier_elementary_bound a ha) b.processL2 =
      (a.boundedProduct b ha).processL2 := by
  apply Lp.ext
  filter_upwards [brownianAdaptedContinuousMultiplierAmbient_coe
    (brownianElementaryProcess_measurable a.left a.right a.coefficient_measurable)
    (brownianAdaptedContinuousMultiplier_elementary_bound a ha) b.processL2,
    b.processL2_coe, (a.boundedProduct b ha).processL2_coe] with p hm hb hp
  rw [hm, hb, hp, brownianAdaptedContinuousMultiplier_elementary_process]

end TimeTraps.Probability

end
