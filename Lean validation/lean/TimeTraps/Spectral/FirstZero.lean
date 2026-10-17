module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Compactness and continuity locate the first loss of positivity in a family.
One-sided derivative signs at a zero minimum will exclude interior/trap zeros
of the exact shooting profile. No existence of a ground state is assumed.
-/

namespace TimeTraps.Spectral

open Set
open scoped Topology

theorem first_nonpositive_parameter {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 < B) (h₀ : 0 < f 0) (hBf : f B ≤ 0) :
    ∃ c ∈ Ioc (0 : ℝ) B, f c = 0 ∧ ∀ k ∈ Ico (0 : ℝ) c, 0 < f k := by
  let bad := Icc (0 : ℝ) B ∩ {k | f k ≤ 0}
  have hcpt : IsCompact bad := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hne : bad.Nonempty := ⟨B, ⟨⟨hB.le, le_rfl⟩, hBf⟩⟩
  obtain ⟨c, hc, hmin⟩ := hcpt.exists_isLeast hne
  have hcp : 0 < c := lt_of_le_of_ne hc.1.1 (by
    intro he
    have hz := hc.2
    rw [← he] at hz
    exact (not_le_of_gt h₀) hz)
  have hbefore : ∀ k ∈ Ico (0 : ℝ) c, 0 < f k := by
    intro k hk
    by_contra h
    exact (not_le_of_gt hk.2) (hmin ⟨⟨hk.1, hk.2.le.trans hc.1.2⟩, le_of_not_gt h⟩)
  have hzero : f c = 0 := by
    apply le_antisymm hc.2
    by_contra h
    have hneg : f c < 0 := lt_of_not_ge h
    obtain ⟨d, hd, he⟩ := intermediate_value_Icc' hcp.le hf.continuousOn
      (show f c / 2 ∈ Icc (f c) (f 0) by constructor <;> linarith)
    have hdc : d < c := lt_of_le_of_ne hd.2 (by
      intro heq
      rw [heq] at he
      linarith)
    have hp := hbefore d ⟨hd.1, hdc⟩
    linarith
  exact ⟨c, ⟨hcp, hc.1.2⟩, hzero, hbefore⟩

theorem compact_first_zero {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) {u : ℝ → X → ℝ}
    (hu : Continuous (fun p : ℝ × X => u p.1 p.2)) {B : ℝ} (hB : 0 < B)
    (h₀ : ∀ x ∈ K, 0 < u 0 x) (hBzero : ∃ x ∈ K, u B x ≤ 0) :
    ∃ c ∈ Ioc (0 : ℝ) B,
      (∀ k ∈ Ico (0 : ℝ) c, ∀ x ∈ K, 0 < u k x) ∧
      (∀ x ∈ K, 0 ≤ u c x) ∧ ∃ x ∈ K, u c x = 0 := by
  let m := fun k => sInf (u k '' K)
  have hum (k : ℝ) : Continuous (u k) := hu.comp (continuous_const.prodMk continuous_id)
  have hm : Continuous m := hK.continuous_sInf hu
  have hm₀ : 0 < m 0 := (hK.lt_sInf_iff_of_continuous hne (hum 0).continuousOn 0).mpr h₀
  have hmB : m B ≤ 0 := by
    obtain ⟨x, hx, hux⟩ := hBzero
    exact (csInf_le (hK.bddBelow_image (hum B).continuousOn) (mem_image_of_mem _ hx)).trans hux
  obtain ⟨c, hc, hmc, hbefore⟩ := first_nonpositive_parameter hm hB hm₀ hmB
  obtain ⟨x, hx, hxm, hxmin⟩ := hK.exists_sInf_image_eq_and_le hne (hum c).continuousOn
  have hxzero : u c x = 0 := hxm.symm.trans hmc
  refine ⟨c, hc, ?_, ?_, x, hx, hxzero⟩
  · intro k hk
    exact (hK.lt_sInf_iff_of_continuous hne (hum k).continuousOn 0).mp (hbefore k hk)
  · intro y hy
    rw [← hxzero]
    exact hxmin y hy

theorem derivative_nonneg_at_left_minimum {f : ℝ → ℝ} {l r d : ℝ}
    (hlr : l < r) (hmin : ∀ x ∈ Icc l r, f l ≤ f x) (hd : HasDerivAt f d l) : 0 ≤ d := by
  have hloc : IsLocalMinOn f (Icc l r) l := (show IsMinOn f (Icc l r) l from hmin).localize
  have hdir : r - l ∈ posTangentConeAt (Icc l r) l :=
    sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_eq_Icc hlr.le])
  have h := hloc.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hdir
  have hm : 0 ≤ (r - l) * d := by simpa using h
  exact nonneg_of_mul_nonneg_right hm (sub_pos.mpr hlr)

theorem derivative_nonpos_at_right_minimum {f : ℝ → ℝ} {l r d : ℝ}
    (hlr : l < r) (hmin : ∀ x ∈ Icc l r, f r ≤ f x) (hd : HasDerivAt f d r) : d ≤ 0 := by
  have hloc : IsLocalMinOn f (Icc l r) r := (show IsMinOn f (Icc l r) r from hmin).localize
  have hdir : l - r ∈ posTangentConeAt (Icc l r) r :=
    sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hlr.le])
  have h := hloc.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hdir
  have hm : 0 ≤ (l - r) * d := by simpa using h
  nlinarith

theorem derivative_zero_at_interior_minimum {f : ℝ → ℝ} {l r x d : ℝ}
    (hx : x ∈ Ioo l r) (hmin : ∀ y ∈ Icc l r, f x ≤ f y) (hd : HasDerivAt f d x) : d = 0 :=
  ((show IsMinOn f (Icc l r) x from hmin).isLocalMin (Icc_mem_nhds hx.1 hx.2)).hasDerivAt_eq_zero hd

end TimeTraps.Spectral
