module

public import TimeTraps.Probability.BrownianIntegralTruncationElementary

@[expose] public section

/-! Deterministic time truncation preserves both the elementary span and
its actual product-L² closure. It therefore defines a linear contraction
on the completed integrand domain. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem brownianTimeCutoffAmbient_mem_stepSpace (t : ℝ≥0)
    {f : Lp ℝ 2 ((volume : Measure ℝ).prod P)}
    (hf : f ∈ brownianIntegralStepSpace B hBm P) :
    brownianTimeCutoffAmbient P t f ∈ brownianIntegralStepSpace B hBm P := by
  have hs : brownianIntegralStepSpace B hBm P ≤
      (brownianIntegralStepSpace B hBm P).comap (brownianTimeCutoffAmbient P t).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change brownianTimeCutoffAmbient P t a.processL2 ∈ brownianIntegralStepSpace B hBm P
    by_cases ht : a.left ≤ t
    · rw [brownianTimeCutoffAmbient_elementary a ht]
      exact Submodule.subset_span ⟨a.refineLeft (min a.right t) (le_min a.ordered ht), rfl⟩
    · rw [brownianTimeCutoffAmbient_elementary_zero a (le_of_not_ge ht)]
      exact (brownianIntegralStepSpace B hBm P).zero_mem
  exact hs hf

theorem brownianTimeCutoffAmbient_mem_space (t : ℝ≥0)
    {f : Lp ℝ 2 ((volume : Measure ℝ).prod P)} (hf : f ∈ brownianIntegralSpace B hBm P) :
    brownianTimeCutoffAmbient P t f ∈ brownianIntegralSpace B hBm P := by
  have hs : brownianIntegralStepSpace B hBm P ≤
      (brownianIntegralSpace B hBm P).comap (brownianTimeCutoffAmbient P t).toLinearMap := by
    intro g hg
    exact Submodule.le_topologicalClosure _ (brownianTimeCutoffAmbient_mem_stepSpace t hg)
  have hc : IsClosed ((brownianIntegralSpace B hBm P).comap
      (brownianTimeCutoffAmbient P t).toLinearMap : Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (Submodule.isClosed_topologicalClosure (brownianIntegralStepSpace B hBm P)).preimage
      (brownianTimeCutoffAmbient P t).continuous
  exact Submodule.topologicalClosure_minimal _ hs hc hf

def brownianTimeCutoff (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) (P : Measure Ω)
    (t : ℝ≥0) : brownianIntegralSpace B hBm P →L[ℝ] brownianIntegralSpace B hBm P :=
  (brownianTimeCutoffAmbient P t).restrict (fun _ hf => brownianTimeCutoffAmbient_mem_space t hf)

theorem brownianTimeCutoff_coe (t : ℝ≥0) (f : brownianIntegralSpace B hBm P) :
    (brownianTimeCutoff B hBm P t f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (brownianTimePast t).indicator (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :=
  brownianTimeCutoffAmbient_coe P t f

theorem brownianTimeCutoff_norm_le (t : ℝ≥0) (f : brownianIntegralSpace B hBm P) :
    ‖brownianTimeCutoff B hBm P t f‖ ≤ ‖f‖ :=
  brownianTimeCutoffAmbient_norm_le P t f

theorem brownianTimeCutoff_generator_zero (a : BrownianIntegralElementary B hBm P)
    {t : ℝ≥0} (ht : t ≤ a.left) : brownianTimeCutoff B hBm P t (brownianIntegralGenerator a) = 0 := by
  apply Subtype.ext
  exact brownianTimeCutoffAmbient_elementary_zero a ht

theorem brownianTimeCutoff_generator (a : BrownianIntegralElementary B hBm P)
    {t : ℝ≥0} (ht : a.left ≤ t) :
    brownianTimeCutoff B hBm P t (brownianIntegralGenerator a) =
      brownianIntegralGenerator (a.refineLeft (min a.right t) (le_min a.ordered ht)) := by
  apply Subtype.ext
  exact brownianTimeCutoffAmbient_elementary a ht

theorem brownianTimeCutoff_generator_full (a : BrownianIntegralElementary B hBm P)
    {t : ℝ≥0} (ht : a.right ≤ t) :
    brownianTimeCutoff B hBm P t (brownianIntegralGenerator a) = brownianIntegralGenerator a := by
  apply Subtype.ext
  exact brownianTimeCutoffAmbient_elementary_full a ht

end TimeTraps.Probability

end
