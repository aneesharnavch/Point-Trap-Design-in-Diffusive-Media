module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.HasLaw

@[expose] public section

/-! A fixed probability law is preserved under actual L2 convergence.
This uses uniqueness of the distributional limit; it does not infer a
Gaussian law from moments or replace convergence by a numerical test. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem real_L2_hasLaw_of_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (U : ℕ → Lp ℝ 2 P) (Y : Lp ℝ 2 P)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlim : Tendsto U atTop (𝓝 Y)) (hlaw : ∀ n, HasLaw (U n) ν P) : HasLaw Y ν P := by
  have hd := (tendstoInMeasure_of_tendsto_Lp hlim).tendstoInDistribution
    (fun n => (Lp.aestronglyMeasurable (U n)).aemeasurable)
  have he (n : ℕ) :
      (⟨P.map (U n), Measure.isProbabilityMeasure_map (hd.forall_aemeasurable n)⟩ : ProbabilityMeasure ℝ) =
        ⟨ν, inferInstance⟩ := by
    apply Subtype.ext
    exact (hlaw n).map_eq
  have hc := hd.tendsto
  simp only [he] at hc
  have hm := tendsto_nhds_unique hc tendsto_const_nhds
  refine ⟨(Lp.aestronglyMeasurable Y).aemeasurable, ?_⟩
  exact congrArg Subtype.val hm

end TimeTraps.Analysis
