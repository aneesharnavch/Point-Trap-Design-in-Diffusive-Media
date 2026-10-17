module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Continuous comparison without derivatives. Local constancy in an
open interval extends to its endpoints. A continuous function initially
nonpositive cannot become positive if it cannot increase over an interval
on which it is positive. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

theorem continuous_eq_endpoints_of_locally_constant_Ioo {f : ℝ → ℝ}
    (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hlocal : ∀ t ∈ Ioo a b, ∀ᶠ s in 𝓝 t, f s = f t) : f b = f a := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hl : IsLocallyConstant (fun t : Ioo a b => f t) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    exact continuous_subtype_val.continuousAt.tendsto.eventually (hlocal t t.property)
  obtain ⟨m, ham, hmb⟩ := exists_between hab
  have he : EqOn f (fun _ => f m) (Ioo a b) := by
    intro t ht
    exact hl.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨m, ham, hmb⟩
  have hc : EqOn f (fun _ => f m) (Icc a b) := by
    simpa only [closure_Ioo hab.ne] using he.closure hf continuous_const
  exact (hc ⟨hab.le, le_rfl⟩).trans (hc ⟨le_rfl, hab.le⟩).symm

theorem continuous_nonpos_of_positive_interval_nonincrease {f : ℝ → ℝ}
    (hf : Continuous f) (hzero : f 0 ≤ 0)
    (hstep : ∀ a b : ℝ, 0 ≤ a → a < b → (∀ t ∈ Ioo a b, 0 < f t) → f b ≤ f a) :
    ∀ T : ℝ, 0 ≤ T → f T ≤ 0 := by
  intro T hT
  by_contra hn
  have hp : 0 < f T := lt_of_not_ge hn
  let bad := Icc (0 : ℝ) T ∩ {t | f t ≤ 0}
  have hc : IsCompact bad := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hne : bad.Nonempty := ⟨0, ⟨⟨le_rfl, hT⟩, hzero⟩⟩
  obtain ⟨a, ha, hmax⟩ := hc.exists_isGreatest hne
  have hab : a < T := lt_of_le_of_ne ha.1.2 (by
    intro he
    have hz := ha.2
    rw [he] at hz
    exact (not_le_of_gt hp) hz)
  have hi : ∀ t ∈ Ioo a T, 0 < f t := by
    intro t ht
    by_contra hnt
    have hta : t ≤ a := hmax ⟨⟨ha.1.1.trans ht.1.le, ht.2.le⟩, le_of_not_gt hnt⟩
    exact (not_le_of_gt ht.1) hta
  exact (not_le_of_gt hp) ((hstep a T ha.1.1 hab hi).trans ha.2)

end TimeTraps.Analysis
