module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
public import Mathlib.Probability.Process.Filtration

@[expose] public section

/-! Independence of each increment from the preceding filtration implies
mutual independence of every finite chronological family of increments.
The process may be adapted only almost everywhere at each fixed time.
Measurable representatives are used inside finite-dimensional arguments;
no completion of the filtration or common uncountable-time event is needed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set

variable {Ω T : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem indep_comap_of_ae_eq (m : MeasurableSpace Ω) {f g : Ω → ℝ}
    (h : Indep (MeasurableSpace.comap f inferInstance) m P) (hfg : f =ᵐ[P] g) :
    Indep (MeasurableSpace.comap g inferInstance) m P := by
  apply (Indep_iff _ _ _).mpr
  rintro _ A ⟨S, hS, rfl⟩ hA
  have he : f ⁻¹' S =ᵐ[P] g ⁻¹' S := hfg.preimage S
  calc
    P (g ⁻¹' S ∩ A) = P (f ⁻¹' S ∩ A) :=
      measure_congr (ae_eq_set_inter he.symm Filter.EventuallyEq.rfl)
    _ = P (f ⁻¹' S) * P A := (Indep_iff _ _ _).mp h _ _ ⟨S, hS, rfl⟩ hA
    _ = P (g ⁻¹' S) * P A := congrArg (fun r => r * P A) (measure_congr he)

theorem adapted_hasIndepIncrements [Preorder T] [IsProbabilityMeasure P]
    (ℱ : Filtration T mΩ) (X : T → Ω → ℝ)
    (hX : ∀ t, Measurable[ℱ t] (X t))
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (ℱ s) P) :
    HasIndepIncrements X P := by
  classical
  intro n τ hτ
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hsets
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert i S hlt ih =>
    have hi : i ∉ S := fun hi => lt_irrefl i (hlt i hi)
    have hs : ∀ j ∈ S, MeasurableSet (sets j) :=
      fun j hj => hsets j (Finset.mem_insert_of_mem hj)
    have hpast : MeasurableSet[ℱ (τ i.castSucc)]
        (⋂ j ∈ S, (fun ω => X (τ j.succ) ω - X (τ j.castSucc) ω) ⁻¹' sets j) := by
      apply Finset.measurableSet_biInter
      intro j hj
      have hjle : j.succ ≤ i.castSucc := by
        change j.val + 1 ≤ i.val
        exact Nat.succ_le_of_lt (hlt j hj)
      have hright : Measurable[ℱ (τ i.castSucc)] (X (τ j.succ)) :=
        (hX _).mono (ℱ.mono (hτ hjle)) le_rfl
      have hleft : Measurable[ℱ (τ i.castSucc)] (X (τ j.castSucc)) :=
        (hX _).mono (ℱ.mono (hτ ((Fin.castSucc_le_succ j).trans hjle))) le_rfl
      exact (hright.sub hleft) (hs j hj)
    rw [Finset.set_biInter_insert, Finset.prod_insert hi]
    rw [(Indep_iff _ _ _).mp (hind _ _ (hτ (Fin.castSucc_le_succ i))) _ _
      ⟨sets i, hsets i (Finset.mem_insert_self _ _), rfl⟩ hpast]
    rw [ih hs]

theorem filteredProcess_hasIndepIncrements [Preorder T] [IsProbabilityMeasure P]
    (ℱ : Filtration T mΩ) (X : T → Ω → ℝ)
    (hX : ∀ t, AEStronglyMeasurable[ℱ t] (X t) P)
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (ℱ s) P) :
    HasIndepIncrements X P := by
  let Y : T → Ω → ℝ := fun t => (hX t).mk (X t)
  have he (t : T) : X t =ᵐ[P] Y t := (hX t).ae_eq_mk
  have hY : HasIndepIncrements Y P :=
    adapted_hasIndepIncrements ℱ Y (fun t => (hX t).measurable_mk)
      (fun s t hst => indep_comap_of_ae_eq (ℱ s) (hind s t hst) ((he t).sub (he s)))
  intro n τ hτ
  exact (hY n τ hτ).congr (fun i => ((he (τ i.succ)).sub (he (τ i.castSucc))).symm)

end TimeTraps.Probability
