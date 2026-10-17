module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

/-! First strict exceedance of a contact threshold. Infinite lifetimes and
flat clock intervals are retained. The survival equivalence at a fixed time
excludes precisely equality with the threshold. -/

namespace TimeTraps.Probability

open Set MeasureTheory

noncomputable def strictKillingTime (A : ℝ → ℝ) (E : ℝ) : WithTop ℝ :=
  hittingAfter (fun t (_ : Unit) => A t) (Ioi E) 0 ()

theorem strictKillingTime_nonneg (A : ℝ → ℝ) (E : ℝ) :
    (0 : WithTop ℝ) ≤ strictKillingTime A E :=
  le_hittingAfter ()

theorem strictKillingTime_eq_top_iff (A : ℝ → ℝ) (E : ℝ) :
    strictKillingTime A E = ⊤ ↔ ∀ t : ℝ, 0 ≤ t → A t ≤ E := by
  simp only [strictKillingTime, hittingAfter_eq_top_iff, mem_Ioi, not_lt]

theorem strictKillingTime_constant (E : ℝ) : strictKillingTime (fun _ => E) E = ⊤ :=
  (strictKillingTime_eq_top_iff _ _).mpr (fun _ _ => le_rfl)

theorem strictKillingTime_le_of_lt (A : ℝ → ℝ) (E t : ℝ) (ht : 0 ≤ t) (hA : E < A t) :
    strictKillingTime A E ≤ (t : WithTop ℝ) :=
  hittingAfter_le_of_mem ht hA

theorem strictKillingTime_gt_of_lt (A : ℝ → ℝ) (E t : ℝ) (ht : 0 ≤ t)
    (hc : ContinuousOn A (Ici (0 : ℝ))) (hm : MonotoneOn A (Ici (0 : ℝ)))
    (hA : A t < E) : (t : WithTop ℝ) < strictKillingTime A E := by
  obtain ⟨δ, hδ, hδA⟩ := Metric.continuousWithinAt_iff.mp (hc t ht)
    (E - A t) (sub_pos.mpr hA)
  let s := t + δ / 2
  have hts : t < s := by dsimp only [s]; linarith
  have hs : s ∈ Ici (0 : ℝ) := ht.trans hts.le
  have hst : dist s t < δ := by
    rw [Real.dist_eq]
    dsimp only [s]
    rw [add_sub_cancel_left, abs_of_pos (div_pos hδ (by norm_num))]
    linarith
  have hAs : A s < E := by
    have hd := hδA hs hst
    rw [Real.dist_eq] at hd
    linarith [(abs_lt.mp hd).2]
  have hle : (s : WithTop ℝ) ≤ strictKillingTime A E := by
    apply le_of_not_gt
    intro hlt
    obtain ⟨j, hj, hAj⟩ := hittingAfter_lt_iff.mp hlt
    have hjs : A j ≤ A s := hm hj.1 hs hj.2.le
    change E < A j at hAj
    linarith
  exact (show (t : WithTop ℝ) < (s : WithTop ℝ) by exact_mod_cast hts).trans_le hle

theorem strictKillingTime_value_le_of_gt (A : ℝ → ℝ) (E t : ℝ) (ht : 0 ≤ t)
    (hτ : (t : WithTop ℝ) < strictKillingTime A E) : A t ≤ E := by
  by_contra h
  exact (not_le_of_gt hτ) (strictKillingTime_le_of_lt A E t ht (lt_of_not_ge h))

theorem strictKillingTime_survival_iff (A : ℝ → ℝ) (E t : ℝ) (ht : 0 ≤ t)
    (hc : ContinuousOn A (Ici (0 : ℝ))) (hm : MonotoneOn A (Ici (0 : ℝ)))
    (hne : A t ≠ E) :
    (t : WithTop ℝ) < strictKillingTime A E ↔ A t < E := by
  constructor
  · intro hτ
    exact lt_of_le_of_ne (strictKillingTime_value_le_of_gt A E t ht hτ) hne
  · exact strictKillingTime_gt_of_lt A E t ht hc hm

end TimeTraps.Probability
