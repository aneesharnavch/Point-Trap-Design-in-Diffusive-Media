module

public import TimeTraps.Probability.ContinuousObservationStoppingData

@[expose] public section

/-! A deterministic transition set-integral identity extends to a
countably valued stopping time by decomposing into its actual level sets. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

theorem continuousObservation_countable_setIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : ℝ≥0 → Ω → ℝ) (hF : StronglyAdapted ℱ F) (hG : StronglyAdapted ℱ G)
    (hcF : ∀ ω, Continuous (fun t => F t ω)) (hcG : ∀ ω, Continuous (fun t => G t ω))
    {CF CG : ℝ} (hbF : ∀ t ω, ‖F t ω‖ ≤ CF) (hbG : ∀ t ω, ‖G t ω‖ ≤ CG)
    (h : ℝ≥0)
    (hdet : ∀ s, ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      (∫ ω in A, G s ω ∂μ) = ∫ ω in A, F (s + h) ω ∂μ)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hcτ : (range τ).Countable) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, G (τ ω) ω ∂μ) = ∫ ω in A, F (τ ω + h) ω ∂μ := by
  let : Countable (range τ) := hcτ.to_subtype
  let B : range τ → Set Ω := fun q => A ∩ {ω | (τ ω : WithTop ℝ≥0) = q.val}
  have hB (q : range τ) : MeasurableSet[ℱ q.val] (B q) :=
    (hτ.measurableSet_inter_eq_iff A q.val).mp (hA.inter (hτ.measurableSet_eq' q.val))
  have hBm (q : range τ) : MeasurableSet (B q) := ℱ.le q.val _ (hB q)
  have hBd : Pairwise (fun q r => Disjoint (B q) (B r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    intro ω hq hr
    apply hqr
    apply Subtype.ext
    exact WithTop.coe_injective (hq.2.symm.trans hr.2)
  have hBu : (⋃ q, B q) = A := by
    ext ω
    simp only [mem_iUnion]
    constructor
    · rintro ⟨q, hq⟩
      exact hq.1
    · intro hω
      exact ⟨⟨τ ω, ⟨ω, rfl⟩⟩, hω, rfl⟩
  have he (q : range τ) : (∫ ω in B q, G (τ ω) ω ∂μ) = ∫ ω in B q, F (τ ω + h) ω ∂μ := by
    calc
      _ = ∫ ω in B q, G q.val ω ∂μ := by
        apply setIntegral_congr_fun (hBm q)
        intro ω hω
        exact congrArg (fun u => G u ω) (WithTop.coe_injective hω.2)
      _ = ∫ ω in B q, F (q.val + h) ω ∂μ := hdet q.val (B q) (hB q)
      _ = _ := by
        apply setIntegral_congr_fun (hBm q)
        intro ω hω
        exact (congrArg (fun u => F (u + h) ω) (WithTop.coe_injective hω.2)).symm
  have hi := (continuousObservation_stopped_integrable μ G hG hcG hbG hτ).integrableOn (s := ⋃ q, B q)
  have hj := (continuousObservation_stopped_integrable μ F hF hcF hbF (finiteStoppingTime_add hτ h)).integrableOn
    (s := ⋃ q, B q)
  rw [← hBu, integral_iUnion hBm hBd hi, integral_iUnion hBm hBd hj]
  exact tsum_congr he

end TimeTraps.Probability
