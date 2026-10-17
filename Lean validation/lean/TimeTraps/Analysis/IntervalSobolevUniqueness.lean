module

public import TimeTraps.Analysis.IntervalSobolev
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section

/-! Uniqueness and a.e. invariance of interval weak derivatives. The
fundamental lemma uses the entire smooth compactly supported test class.
No regularity or pointwise derivative of a weak Sobolev representative is
assumed in these results. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Function Filter
open scoped Topology ContDiff

theorem intervalSobolev_test_pairing_integrable {g φ : ℝ → ℝ} {l r : ℝ}
    (hg : LocallyIntegrableOn g (Ioo l r)) (hφ : Continuous φ)
    (hk : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo l r) :
    Integrable (fun x => g x * φ x) := by
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    ((hg.integrableOn_compact_subset hs hk).mul_continuousOn hφ.continuousOn hk)
  intro x hx
  apply subset_closure
  intro hz
  exact hx (by simp [hz])

/-- Distributional weak derivatives, when locally integrable, are unique
almost everywhere on the open interval. -/
theorem IntervalWeakDerivative.unique {u g h : ℝ → ℝ} {l r : ℝ}
    (hg : IntervalWeakDerivative u g l r) (hh : IntervalWeakDerivative u h l r)
    (hgi : LocallyIntegrableOn g (Ioo l r)) (hhi : LocallyIntegrableOn h (Ioo l r)) :
    g =ᵐ[volume.restrict (Ioo l r)] h := by
  have hz : ∀ᵐ x, x ∈ Ioo l r → (g - h) x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hgi.sub hhi)
    intro φ hc hk hs
    have hgp := intervalSobolev_test_pairing_integrable hgi hc.continuous hk hs
    have hhp := intervalSobolev_test_pairing_integrable hhi hc.continuous hk hs
    have he : (∫ x, φ x • (g - h) x) =
        (∫ x, g x * φ x) - ∫ x, h x * φ x := by
      calc
        _ = ∫ x, g x * φ x - h x * φ x := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [smul_eq_mul, Pi.sub_apply]
          ring
        _ = _ := integral_sub hgp hhp
    rw [he]
    have h₁ := hg φ hc hk hs
    have h₂ := hh φ hc hk hs
    linarith
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hz] with x hx
  intro hxm
  exact sub_eq_zero.mp (hx hxm)

theorem intervalSobolev_test_pairing_congr {f g φ : ℝ → ℝ} {l r : ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioo l r)] g) (hs : tsupport φ ⊆ Ioo l r) :
    (∫ x, f x * φ x) = ∫ x, g x * φ x := by
  have h := (ae_restrict_iff' measurableSet_Ioo).mp hfg
  apply integral_congr_ae
  filter_upwards [h] with x hx
  by_cases hm : x ∈ Ioo l r
  · rw [hx hm]
  · have hz : φ x = 0 := by
      by_contra hn
      exact hm (hs (subset_closure hn))
    simp only [hz, mul_zero]

/-- Weak differentiation is a property of a.e. classes, even though the
eventual absolutely continuous representative is pointwise continuous. -/
theorem IntervalWeakDerivative.congr_ae {u v g h : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalWeakDerivative u g l r)
    (huv : u =ᵐ[volume.restrict (Ioo l r)] v)
    (hgh : g =ᵐ[volume.restrict (Ioo l r)] h) : IntervalWeakDerivative v h l r := by
  intro φ hc hk hs
  rw [← intervalSobolev_test_pairing_congr huv (tsupport_deriv_subset.trans hs),
    ← intervalSobolev_test_pairing_congr hgh hs]
  exact hu φ hc hk hs

theorem IntervalSobolev.congr_ae {u v : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalSobolev u l r) (huv : u =ᵐ[volume.restrict (Ioo l r)] v) :
    IntervalSobolev v l r := by
  obtain ⟨hu₂, g, hg₂, hd⟩ := hu
  exact ⟨hu₂.ae_eq huv, g, hg₂, hd.congr_ae huv (Filter.EventuallyEq.rfl)⟩

/-- For an energy representative there are no other L2 weak derivatives
than its actual a.e. derivative. -/
theorem IntervalEnergy.weakDerivative_iff {u g : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l ≤ r)
    (hg : MemLp g 2 (volume.restrict (Ioo l r))) :
    IntervalWeakDerivative u g l r ↔ g =ᵐ[volume.restrict (Ioo l r)] deriv u := by
  have hd : MemLp (deriv u) 2 (volume.restrict (Ioo l r)) := by
    apply hu.derivative_memLp.mono_measure
    rw [uIoc_of_le hlr]
    exact Measure.restrict_mono_set volume Ioo_subset_Ioc_self
  constructor
  · intro h
    exact h.unique (hu.weakDerivative hlr)
      (show IntegrableOn g (Ioo l r) volume from hg.integrable (by norm_num)).locallyIntegrableOn
      (show IntegrableOn (deriv u) (Ioo l r) volume from hd.integrable (by norm_num)).locallyIntegrableOn
  · intro h
    exact (hu.weakDerivative hlr).congr_ae Filter.EventuallyEq.rfl h.symm

end TimeTraps.Analysis
