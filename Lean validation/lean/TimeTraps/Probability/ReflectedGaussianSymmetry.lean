module

public import TimeTraps.Probability.ReflectedGaussianRegularity

@[expose] public section

/-! Symmetry of the actual Gaussian image kernel. The first family of
images is reindexed by integer negation, while the second family is
symmetric term by term. The density is jointly measurable in its two
spatial arguments. Its interpretation as a probability density continues
to require positive variance; the algebraic symmetry itself does not. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedGaussianKernel_symmetric (L x y : ℝ) (v : ℝ≥0) :
    reflectedGaussianKernel L x v y = reflectedGaussianKernel L y v x := by
  unfold reflectedGaussianKernel reflectedFoldDensity
  rw [ENNReal.tsum_add, ENNReal.tsum_add]
  have hp : (∑' k : ℤ, gaussianPDF x v (y + k * (2 * L))) =
      ∑' k : ℤ, gaussianPDF y v (x + k * (2 * L)) := by
    calc
      _ = ∑' k : ℤ, gaussianPDF x v (y + ((-k : ℤ) : ℝ) * (2 * L)) :=
        ((Equiv.neg ℤ).tsum_eq (fun k : ℤ => gaussianPDF x v (y + k * (2 * L)))).symm
      _ = _ := by
        apply tsum_congr
        intro k
        unfold gaussianPDF gaussianPDFReal
        congr 3
        push_cast
        ring
  have hm : (∑' k : ℤ, gaussianPDF x v (k * (2 * L) - y)) =
      ∑' k : ℤ, gaussianPDF y v (k * (2 * L) - x) := by
    apply tsum_congr
    intro k
    unfold gaussianPDF gaussianPDFReal
    congr 3
    ring
  rw [hp, hm]

theorem reflectedGaussianDensity_symmetric (L x y : ℝ) (v : ℝ≥0) :
    reflectedGaussianDensity L x v y = reflectedGaussianDensity L y v x := by
  unfold reflectedGaussianDensity
  rw [reflectedGaussianKernel_symmetric]

theorem reflectedGaussianKernel_jointlyMeasurable (L : ℝ) (v : ℝ≥0) :
    Measurable (fun p : ℝ × ℝ => reflectedGaussianKernel L p.1 v p.2) := by
  unfold reflectedGaussianKernel reflectedFoldDensity gaussianPDF gaussianPDFReal
  apply Measurable.tsum
  intro k
  fun_prop

end TimeTraps.Probability
