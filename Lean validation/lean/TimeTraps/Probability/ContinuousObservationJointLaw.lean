module

public import TimeTraps.Probability.BoundedContinuousLaplaceMeasure
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! A finite joint law is determined by continuous observations of its
real final coordinate restricted to arbitrary measurable past events. No
regular conditional distribution is required for this elementary step. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped BoundedContinuousFunction

theorem jointLaw_eq_of_restricted_continuous_observations
    {Ω Ω' Z : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} [MeasurableSpace Z]
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {P : Ω → Z} {Q : Ω' → Z} {U : Ω → ℝ} {V : Ω' → ℝ}
    (hP : Measurable P) (hQ : Measurable Q) (hU : Measurable U) (hV : Measurable V)
    (heq : ∀ E : Set Z, MeasurableSet E → ∀ f : ℝ →ᵇ ℝ,
      (∫ ω in P ⁻¹' E, f (U ω) ∂μ) = ∫ ω in Q ⁻¹' E, f (V ω) ∂ν) :
    μ.map (fun ω => (P ω, U ω)) = ν.map (fun ω => (Q ω, V ω)) := by
  apply Measure.ext_prod
  intro E B hE hB
  have hrest : (μ.restrict (P ⁻¹' E)).map U = (ν.restrict (Q ⁻¹' E)).map V := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map hU.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map hV.aemeasurable f.continuous.aestronglyMeasurable]
    exact heq E hE f
  have he := congrArg (fun ρ : Measure ℝ => ρ B) hrest
  rw [Measure.map_apply hU hB, Measure.map_apply hV hB,
    Measure.restrict_apply (hU hB), Measure.restrict_apply (hV hB)] at he
  rw [Measure.map_apply (hP.prodMk hU) (hE.prod hB),
    Measure.map_apply (hQ.prodMk hV) (hE.prod hB)]
  have hleft : (fun ω => (P ω, U ω)) ⁻¹' (E ×ˢ B) = U ⁻¹' B ∩ P ⁻¹' E := by
    ext ω
    simp only [mem_preimage, mem_prod, mem_inter_iff, and_comm]
  have hright : (fun ω => (Q ω, V ω)) ⁻¹' (E ×ˢ B) = V ⁻¹' B ∩ Q ⁻¹' E := by
    ext ω
    simp only [mem_preimage, mem_prod, mem_inter_iff, and_comm]
  exact (congrArg μ hleft).trans (he.trans (congrArg ν hright).symm)

end TimeTraps.Probability

end
