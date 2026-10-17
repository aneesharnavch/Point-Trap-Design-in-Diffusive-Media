module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovStoppingClockData

@[expose] public section

/-! A continuous increasing family of finite stopping times can be
sampled at any finite stopping time of its stopped filtration. Upper-grid
approximation and right continuity prove both the stopping property and
the inclusion of stopped sigma-fields; neither is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter Classical
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem sampledClock_restricted_isStoppingTime
    {F G : Filtration ℝ≥0 mΩ} [F.IsRightContinuous] {T : ℝ≥0 → Ω → ℝ≥0}
    (hT : ∀ t, IsStoppingTime F (fun ω => (T t ω : WithTop ℝ≥0)))
    (hG : ∀ t, G t = (hT t).measurableSpace)
    (hmono : ∀ ω, Monotone (fun t => T t ω))
    (hcont : ∀ ω, Continuous (fun t => T t ω))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime G (fun ω => (σ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    IsStoppingTime F (fun ω => if ω ∈ A then (T (σ ω) ω : WithTop ℝ≥0) else ⊤) := by
  let σn : ℕ → Ω → ℝ≥0 := fun n ω => boundedStoppingUpperGrid n (σ ω)
  have hn (n : ℕ) : IsStoppingTime G (fun ω => (σn n ω : WithTop ℝ≥0)) :=
    boundedStoppingUpperGrid_isStoppingTime hσ n
  have hAn (n : ℕ) : MeasurableSet[(hn n).measurableSpace] A :=
    hσ.measurableSpace_mono (hn n)
      (fun ω => WithTop.coe_le_coe.mpr (boundedStoppingUpperGrid_bounds n (σ ω)).1) A hA
  have hstop (n : ℕ) : IsStoppingTime F
      (fun ω => if ω ∈ A then (T (σn n ω) ω : WithTop ℝ≥0) else ⊤) :=
    sampledClock_countable_restricted_isStoppingTime hT hG (hn n)
      (sampledClock_upperGrid_countable σ n) (hAn n)
  have hi := IsStoppingTime.iInf hstop
  have he : (fun ω => ⨅ n : ℕ, if ω ∈ A then (T (σn n ω) ω : WithTop ℝ≥0) else ⊤) =
      (fun ω => if ω ∈ A then (T (σ ω) ω : WithTop ℝ≥0) else ⊤) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [if_pos hω]
      exact sampledClock_upperGrid_iInf hmono hcont σ ω
    · simp only [if_neg hω, iInf_const]
  rwa [he] at hi

theorem sampledClock_isStoppingTime
    {F G : Filtration ℝ≥0 mΩ} [F.IsRightContinuous] {T : ℝ≥0 → Ω → ℝ≥0}
    (hT : ∀ t, IsStoppingTime F (fun ω => (T t ω : WithTop ℝ≥0)))
    (hG : ∀ t, G t = (hT t).measurableSpace)
    (hmono : ∀ ω, Monotone (fun t => T t ω))
    (hcont : ∀ ω, Continuous (fun t => T t ω))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime G (fun ω => (σ ω : WithTop ℝ≥0))) :
    IsStoppingTime F (fun ω => (T (σ ω) ω : WithTop ℝ≥0)) := by
  simpa only [mem_univ, if_true] using
    sampledClock_restricted_isStoppingTime hT hG hmono hcont hσ (A := univ) MeasurableSet.univ

theorem sampledClock_stopped_measurableSpace_le
    {F G : Filtration ℝ≥0 mΩ} [F.IsRightContinuous] {T : ℝ≥0 → Ω → ℝ≥0}
    (hT : ∀ t, IsStoppingTime F (fun ω => (T t ω : WithTop ℝ≥0)))
    (hG : ∀ t, G t = (hT t).measurableSpace)
    (hmono : ∀ ω, Monotone (fun t => T t ω))
    (hcont : ∀ ω, Continuous (fun t => T t ω))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime G (fun ω => (σ ω : WithTop ℝ≥0))) :
    hσ.measurableSpace ≤ (sampledClock_isStoppingTime hT hG hmono hcont hσ).measurableSpace := by
  intro A hA
  have hsup : (⨆ t, G t) ≤ ⨆ t, F t :=
    iSup_le (fun t => (hG t).le.trans (hT t).measurableSpace_le')
  refine ⟨hsup A (hσ.measurableSpace_le' A hA), fun r => ?_⟩
  have h := sampledClock_restricted_isStoppingTime hT hG hmono hcont hσ hA r
  have he : {ω | (if ω ∈ A then (T (σ ω) ω : WithTop ℝ≥0) else ⊤) ≤ r} =
      A ∩ {ω | (T (σ ω) ω : WithTop ℝ≥0) ≤ r} := by
    ext ω
    by_cases hω : ω ∈ A
    · simp only [mem_ofPred_eq, mem_inter_iff, hω, if_true, true_and]
    · simp only [mem_ofPred_eq, mem_inter_iff, hω, if_false, false_and, iff_false]
      exact WithTop.not_top_le_coe r
  rwa [he] at h

end TimeTraps.Probability

end
