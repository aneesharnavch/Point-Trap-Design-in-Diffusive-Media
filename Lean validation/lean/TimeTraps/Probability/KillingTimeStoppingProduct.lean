module

public import TimeTraps.Probability.KillingTimeStopping
public import TimeTraps.Probability.KillingTimeSurvival

@[expose] public section

/-! Product filtration for an independent exponential killing threshold.
The full threshold is revealed at time zero. The path filtration is lifted
without changing the product probability law. Its right-continuous hull
gives an actual stopping time, without assuming that product sigma algebras
commute with right limits. -/

namespace TimeTraps.Probability

open Set MeasureTheory

variable {Ω : Type*} [m : MeasurableSpace Ω]

def exponentialKillingFiltration (F : Filtration ℝ m) :
    Filtration ℝ (inferInstance : MeasurableSpace (Ω × ℝ)) where
  seq t := (F t).prod (inferInstance : MeasurableSpace ℝ)
  mono' := fun _ _ h => sup_le_sup (MeasurableSpace.comap_mono (F.mono h)) le_rfl
  le' := fun t => sup_le_sup (MeasurableSpace.comap_mono (F.le t)) le_rfl

theorem exponentialKillingFiltration_path (F : Filtration ℝ m) (t : ℝ) :
    Measurable[(exponentialKillingFiltration F) t, F t] (Prod.fst : Ω × ℝ → Ω) :=
  measurable_fst

theorem exponentialKillingFiltration_threshold (F : Filtration ℝ m) (t : ℝ) :
    Measurable[(exponentialKillingFiltration F) t] (Prod.snd : Ω × ℝ → ℝ) :=
  measurable_snd

theorem exponentialKillingFiltration_adapted (F : Filtration ℝ m) (A : ℝ → Ω → ℝ)
    (hA : Adapted F A) :
    Adapted (exponentialKillingFiltration F) (fun t p => A t p.1) := by
  intro t
  exact (hA t).comp (exponentialKillingFiltration_path F t)

theorem contactLifetime_isStoppingTime_product (F : Filtration ℝ m)
    [(exponentialKillingFiltration F).IsRightContinuous] (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable[F t] (A t))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    IsStoppingTime (exponentialKillingFiltration F) (contactLifetime A) := by
  exact strictKillingTime_isStoppingTime (exponentialKillingFiltration F)
    (fun t p => A t p.1) Prod.snd
    (fun t ht => (hA t ht).comp (exponentialKillingFiltration_path F t))
    (exponentialKillingFiltration_threshold F 0) (fun p => hm p.1)

theorem contactLifetime_isStoppingTime_product_rightCont (F : Filtration ℝ m)
    (A : ℝ → Ω → ℝ) (hA : ∀ t : ℝ, 0 ≤ t → Measurable[F t] (A t))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    IsStoppingTime (exponentialKillingFiltration F).rightCont (contactLifetime A) := by
  exact strictKillingTime_isStoppingTime_rightCont (exponentialKillingFiltration F)
    (fun t p => A t p.1) Prod.snd
    (fun t ht => (hA t ht).comp (exponentialKillingFiltration_path F t))
    (exponentialKillingFiltration_threshold F 0) (fun p => hm p.1)

theorem exponentialKilling_stopping_construction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℝ m) (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable[F t] (A t))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    Measurable[(exponentialKillingFiltration F).rightCont 0] (Prod.snd : Ω × ℝ → ℝ) ∧
      ProbabilityTheory.IndepFun (Prod.fst : Ω × ℝ → Ω) Prod.snd (exponentialKillingMeasure μ) ∧
      IsStoppingTime (exponentialKillingFiltration F).rightCont (contactLifetime A) := by
  refine ⟨(exponentialKillingFiltration_threshold F 0).mono
    ((exponentialKillingFiltration F).le_rightCont 0) le_rfl, ?_, ?_⟩
  · exact exponentialKilling_independent μ
  · exact contactLifetime_isStoppingTime_product_rightCont F A hA hm

end TimeTraps.Probability
