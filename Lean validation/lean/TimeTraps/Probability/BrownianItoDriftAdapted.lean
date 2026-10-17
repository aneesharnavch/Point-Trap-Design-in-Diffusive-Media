module

public import TimeTraps.Probability.BrownianItoDriftApproximation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

/-! The actual ordinary time integral of a Lipschitz function of
Brownian motion has a representative measurable in the raw past.
This follows from the proved L2 convergence of adapted dyadic time sums
and closedness of the raw-measurable L2 subspace. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

theorem brownianItoDriftSum_stronglyMeasurable_past (hBm : ∀ t, Measurable (B t))
    (hg : LipschitzWith K g) (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[brownianNaturalFiltration B hBm T] (brownianItoDriftSum B g T n) := by
  unfold brownianItoDriftSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have ht : brownianDyadicGrid T n i.castSucc ≤ T := by
    simpa only [brownianDyadicGrid_last] using
      brownianDyadicGrid_monotone T n (Fin.le_last i.castSucc)
  exact (hg.continuous.comp_stronglyMeasurable
    ((brownianNaturalFiltration_stronglyAdapted B hBm _).mono
      ((brownianNaturalFiltration B hBm).mono ht))).const_mul _

theorem brownianItoDrift_aestronglyMeasurable_past (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm T] (brownianItoDrift B g T) P := by
  have hc := isClosed_aestronglyMeasurable (F := ℝ) (p := (2 : ℝ≥0∞)) (μ := P)
    ((brownianNaturalFiltration B hBm).le T)
  have hlim := brownianItoDriftL2_tendsto hB hBm hg hjoint T
  have hm : AEStronglyMeasurable[brownianNaturalFiltration B hBm T]
      (brownianItoDriftL2 B g T (brownianItoDrift_memLp hB hg hjoint T)) P := by
    apply hc.mem_of_tendsto hlim
    exact Eventually.of_forall (fun n =>
      (brownianItoDriftSum_stronglyMeasurable_past hBm hg T n).aestronglyMeasurable.congr
        (brownianItoDriftSumL2_coe B g T n (brownianItoDriftSum_memLp hB hg T n)).symm)
  exact hm.congr (brownianItoDriftL2_coe B g T (brownianItoDrift_memLp hB hg hjoint T))

theorem brownianItoDrift_condExp_past (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) {T s : ℝ≥0} (hTs : T ≤ s) :
    P[brownianItoDrift B g T | brownianNaturalFiltration B hBm s] =ᵐ[P] brownianItoDrift B g T := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply condExp_of_aestronglyMeasurable' ((brownianNaturalFiltration B hBm).le s)
    ((brownianItoDrift_aestronglyMeasurable_past hB hBm hg hjoint T).mono
      ((brownianNaturalFiltration B hBm).mono hTs))
  exact (brownianItoDrift_memLp hB hg hjoint T).integrable (by norm_num)

end TimeTraps.Probability
