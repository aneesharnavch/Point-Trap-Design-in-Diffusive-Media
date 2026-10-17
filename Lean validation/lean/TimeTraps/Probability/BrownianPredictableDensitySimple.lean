module

public import TimeTraps.Probability.BrownianPredictableDensitySets
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

@[expose] public section

/-! Simple predictable functions are finite linear combinations of the
predictable-set indicators already proved to lie in the integral space. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem brownianPredictableSimple_value_sum {α : Type*} [MeasurableSpace α]
    (f : SimpleFunc α ℝ) (x : α) :
    f x = ∑ c ∈ f.range, c * (f ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) x := by
  classical
  symm
  calc
    _ = f x * (f ⁻¹' {f x}).indicator (fun _ => (1 : ℝ)) x := by
      apply Finset.sum_eq_single (f x)
      · intro c _ hcx
        rw [indicator_of_notMem (by simpa only [mem_preimage, mem_singleton_iff] using hcx.symm),
          mul_zero]
      · intro h
        exact (h (f.mem_range_self x)).elim
    _ = f x := by rw [indicator_of_mem (by rfl), mul_one]

theorem brownianPredictableSimple_cutoff_sum {Ω : Type*}
    {m : MeasurableSpace (ℝ≥0 × Ω)} (T : ℝ≥0) (f : @SimpleFunc (ℝ≥0 × Ω) m ℝ) :
    brownianSquareProcess (fun t ω => f (t, ω)) T =
      ∑ c ∈ f.range, c • brownianPredictableCutoffIndicator T (f ⁻¹' {c}) := by
  classical
  funext p
  simp only [brownianSquareProcess, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    brownianPredictableCutoffIndicator]
  calc
    _ = (Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1 *
        (∑ c ∈ f.range, c * (f ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) (p.1.toNNReal, p.2)) :=
      congrArg (fun r => (Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1 * r)
        (brownianPredictableSimple_value_sum f (p.1.toNNReal, p.2))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      change _ = c * ((Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1 * _)
      ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable [IsFiniteMeasure P]

theorem brownianPredictableDensityMember_simple (T : ℝ≥0)
    (f : @SimpleFunc (ℝ≥0 × Ω) (brownianNaturalFiltration B hBm).predictable ℝ) :
    BrownianPredictableDensityMember B hBm P (brownianSquareProcess (fun t ω => f (t, ω)) T) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := (brownianNaturalFiltration B hBm).predictable
  rw [brownianPredictableSimple_cutoff_sum]
  apply brownianPredictableDensityMember_sum
  intro c _
  exact brownianPredictableDensityMember_smul
    (brownianPredictableDensityMember_indicator T (f ⁻¹' {c}) (f.measurableSet_fiber c)) c

end TimeTraps.Probability
