module

public import TimeTraps.Analysis.IntervalSobolevUniqueness
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-! Smooth test functions used to recover an absolutely continuous
representative from a distributional weak derivative. A smooth test with
zero integral has a smooth primitive compactly supported in the same open
interval. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Function
open scoped Topology ContDiff

theorem intervalSobolev_test_support_bounds {φ : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hk : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo l r) :
    ∃ a b : ℝ, l < a ∧ a < b ∧ b < r ∧ tsupport φ ⊆ Ioo a b := by
  by_cases hn : (tsupport φ).Nonempty
  · obtain ⟨c, hc, hmin⟩ := hk.exists_isMinOn hn continuousOn_id
    obtain ⟨d, hd, hmax⟩ := hk.exists_isMaxOn hn continuousOn_id
    have hcd : c ≤ d := hmin hd
    have hlc := (hs hc).1
    have hdr := (hs hd).2
    refine ⟨(l + c) / 2, (d + r) / 2, by linarith, by linarith, by linarith, ?_⟩
    intro x hx
    have hcx : c ≤ x := hmin hx
    have hxd : x ≤ d := hmax hx
    constructor <;> linarith
  · refine ⟨(2 * l + r) / 3, (l + 2 * r) / 3, by linarith, by linarith, by linarith, ?_⟩
    exact (Set.not_nonempty_iff_eq_empty.mp hn) ▸ empty_subset _

theorem intervalSobolev_test_primitive {φ : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hc : ContDiff ℝ ∞ φ) (hk : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo l r) (hzero : (∫ x, φ x) = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo l r ∧ deriv ψ = φ := by
  obtain ⟨a, b, hla, hab, hbr, hsab⟩ := intervalSobolev_test_support_bounds hlr hk hs
  let ψ : ℝ → ℝ := fun x => ∫ t in a..x, φ t
  have hd (x : ℝ) : HasDerivAt ψ (φ x) x :=
    (hc.continuous.integral_hasStrictDerivAt a x).hasDerivAt
  have hderiv : deriv ψ = φ := funext fun x => (hd x).deriv
  have hleft {x : ℝ} (hx : x ≤ a) : ψ x = 0 := by
    have hi : (∫ t in x..a, φ t) = 0 := by
      calc
        _ = ∫ t in x..a, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hx
          intro t ht
          by_contra hn
          have ha : a < t := (hsab (subset_closure hn)).1
          linarith [ht.2]
        _ = 0 := by simp
    change (∫ t in a..x, φ t) = 0
    rw [intervalIntegral.integral_symm, hi, neg_zero]
  have hright {x : ℝ} (hx : b ≤ x) : ψ x = 0 := by
    have hi : (∫ t in b..x, φ t) = 0 := by
      calc
        _ = ∫ t in b..x, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hx
          intro t ht
          by_contra hn
          have hb : t < b := (hsab (subset_closure hn)).2
          linarith [ht.1]
        _ = 0 := by simp
    have habzero : (∫ t in a..b, φ t) = 0 := by
      have hp := intervalSobolev_test_integral (f := fun _ => (1 : ℝ)) hab.le hsab
      simpa only [one_mul, hzero] using hp
    change (∫ t in a..x, φ t) = 0
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.continuous.intervalIntegrable a b) (hc.continuous.intervalIntegrable b x), habzero, hi, add_zero]
  have hsupport : support ψ ⊆ Icc a b := by
    intro x hx
    constructor
    · by_contra hn
      exact hx (hleft (le_of_lt (lt_of_not_ge hn)))
    · by_contra hn
      exact hx (hright (le_of_lt (lt_of_not_ge hn)))
  have htsupport : tsupport ψ ⊆ Icc a b := closure_minimal hsupport isClosed_Icc
  refine ⟨ψ, ?_, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport,
    ?_, hderiv⟩
  · apply contDiff_infty_iff_deriv.mpr
    exact ⟨fun x => (hd x).differentiableAt, hderiv ▸ hc⟩
  · intro x hx
    have hi := htsupport hx
    exact ⟨hla.trans_le hi.1, hi.2.trans_lt hbr⟩

theorem intervalSobolev_unit_test {l r : ℝ} (hlr : l < r) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo l r ∧ (∫ x, η x) = 1 := by
  have hm : (l + r) / 2 ∈ Ioo l r := by constructor <;> linarith
  obtain ⟨φ, hs, hk, hc, hn, hone⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (isOpen_Ioo.mem_nhds hm)
  have hpos : 0 < ∫ x, φ x :=
    hc.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hk
      (fun x => (hn (mem_range_self x)).1) (by rw [hone]; norm_num)
  have hsupport : support (fun x => φ x / ∫ t, φ t) ⊆ tsupport φ := by
    intro x hx
    apply subset_closure
    intro hz
    exact hx (by simp [hz])
  refine ⟨fun x => φ x / ∫ t, φ t, hc.div_const _, ?_, ?_, ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact hk hsupport
  · exact (closure_minimal hsupport isClosed_closure).trans hs
  · rw [integral_div, div_self hpos.ne']

end TimeTraps.Analysis
