module

public import TimeTraps.Probability.BrownianIntegralConditional

@[expose] public section

/-! Integrands in the closed span of elementary processes ending by t
have stochastic integrals with raw-F_t-measurable representatives. This
is an almost-everywhere representative statement, as appropriate for L2. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def brownianIntegralPastSpace (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (P : Measure Ω) (t : ℝ≥0) :
    Submodule ℝ (brownianIntegralSpace B hBm P) :=
  (Submodule.span ℝ (Set.range (fun a : {a : BrownianIntegralElementary B hBm P // a.right ≤ t} =>
    brownianIntegralGenerator a.1))).topologicalClosure

variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem BrownianIntegralElementary.integralL2_aestronglyMeasurable_past
    (hB : IsPreBrownianReal B P) (a : BrownianIntegralElementary B hBm P)
    {t : ℝ≥0} (ht : a.right ≤ t) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (a.integralL2 hB) P := by
  have hlt := (brownianNaturalFiltration B hBm).mono (a.ordered.trans ht)
  have hrt := (brownianNaturalFiltration B hBm).mono ht
  have hc : StronglyMeasurable[brownianNaturalFiltration B hBm t]
      (fun ω => a.coefficient ω * (B a.right ω - B a.left ω)) :=
    (a.adapted.mono hlt).mul
      (((brownianNaturalFiltration_stronglyAdapted B hBm a.right).mono hrt).sub
        ((brownianNaturalFiltration_stronglyAdapted B hBm a.left).mono hlt))
  exact hc.aestronglyMeasurable.congr (a.integralL2_coe hB).symm

theorem brownianIntegralGenerator_mem_past (a : BrownianIntegralElementary B hBm P)
    {t : ℝ≥0} (ht : a.right ≤ t) :
    brownianIntegralGenerator a ∈ brownianIntegralPastSpace B hBm P t :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨a, ht⟩, rfl⟩)

theorem brownianIntegral_condExp_past (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) (hf : f ∈ brownianIntegralPastSpace B hBm P t) :
    P[brownianIntegral hB f | brownianNaturalFiltration B hBm t] =ᵐ[P] brownianIntegral hB f := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hgen (a : BrownianIntegralElementary B hBm P) (ha : a.right ≤ t) :
      brownianIntegralCondExpL2 hB t (brownianIntegralGenerator a) =
        brownianIntegral hB (brownianIntegralGenerator a) := by
    apply Lp.ext
    refine (brownianIntegralCondExpL2_ae hB t (brownianIntegralGenerator a)).trans ?_
    rw [brownianIntegral_generator]
    exact condExp_of_aestronglyMeasurable' ((brownianNaturalFiltration B hBm).le t)
      (a.integralL2_aestronglyMeasurable_past hB ha)
      ((Lp.memLp (a.integralL2 hB)).integrable (by norm_num))
  let difference : brownianIntegralSpace B hBm P →L[ℝ] Lp ℝ 2 P :=
    brownianIntegralCondExpL2 hB t - (brownianIntegral hB).toContinuousLinearMap
  have hs : Submodule.span ℝ (Set.range
      (fun a : {a : BrownianIntegralElementary B hBm P // a.right ≤ t} =>
        brownianIntegralGenerator a.1)) ≤ difference.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change brownianIntegralCondExpL2 hB t (brownianIntegralGenerator a.1) -
      brownianIntegral hB (brownianIntegralGenerator a.1) = 0
    exact sub_eq_zero.mpr (hgen a.1 a.2)
  have hz : difference f = 0 :=
    Submodule.topologicalClosure_minimal _ hs difference.isClosed_ker hf
  have he : brownianIntegralCondExpL2 hB t f = brownianIntegral hB f := sub_eq_zero.mp hz
  have hae := brownianIntegralCondExpL2_ae hB t f
  rw [he] at hae
  exact hae.symm

theorem brownianIntegral_aestronglyMeasurable_past (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) (hf : f ∈ brownianIntegralPastSpace B hBm P t) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (brownianIntegral hB f) P :=
  stronglyMeasurable_condExp.aestronglyMeasurable.congr (brownianIntegral_condExp_past hB t f hf)

/-- An actual representative measurable in the raw natural filtration. -/
theorem brownianIntegral_past_representative (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) (hf : f ∈ brownianIntegralPastSpace B hBm P t) :
    ∃ g : Ω → ℝ, StronglyMeasurable[brownianNaturalFiltration B hBm t] g ∧
      brownianIntegral hB f =ᵐ[P] g :=
  ⟨P[brownianIntegral hB f | brownianNaturalFiltration B hBm t], stronglyMeasurable_condExp,
    (brownianIntegral_condExp_past hB t f hf).symm⟩

end TimeTraps.Probability
