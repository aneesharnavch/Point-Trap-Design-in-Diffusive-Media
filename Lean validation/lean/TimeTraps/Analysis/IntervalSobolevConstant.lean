module

public import TimeTraps.Analysis.IntervalSobolevTests

@[expose] public section

/-! A locally integrable function with zero distributional derivative on
an interval is constant almost everywhere. The proof uses all smooth
compactly supported tests and constructs primitives of zero-mean tests. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Function Filter
open scoped Topology ContDiff

theorem IntervalWeakDerivative.ae_constant {u : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hu : IntervalWeakDerivative u (fun _ => 0) l r)
    (hi : LocallyIntegrableOn u (Ioo l r)) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo l r)] fun _ => c := by
  obtain ⟨η, hηc, hηk, hηs, hηone⟩ := intervalSobolev_unit_test hlr
  let c : ℝ := ∫ x, u x * η x
  have hηi : Integrable η := hηc.continuous.integrable_of_hasCompactSupport hηk
  have huη := intervalSobolev_test_pairing_integrable hi hηc.continuous hηk hηs
  have hpair (φ : ℝ → ℝ) (hc : ContDiff ℝ ∞ φ) (hk : HasCompactSupport φ)
      (hs : tsupport φ ⊆ Ioo l r) : (∫ x, u x * φ x) = (∫ x, φ x) * c := by
    let θ : ℝ → ℝ := fun x => φ x - (∫ t, φ t) * η x
    have hθc : ContDiff ℝ ∞ θ := hc.sub (contDiff_const.mul hηc)
    have hsupport : support θ ⊆ tsupport φ ∪ tsupport η := by
      intro x hx
      by_contra hn
      have hp : φ x = 0 := by
        by_contra hp
        exact hn (Or.inl (subset_closure hp))
      have he : η x = 0 := by
        by_contra he
        exact hn (Or.inr (subset_closure he))
      exact hx (by simp [θ, hp, he])
    have hθk : HasCompactSupport θ :=
      HasCompactSupport.of_support_subset_isCompact (hk.union hηk) hsupport
    have hθs : tsupport θ ⊆ Ioo l r :=
      (closure_minimal hsupport (isClosed_closure.union isClosed_closure)).trans
        (union_subset hs hηs)
    have hφi : Integrable φ := hc.continuous.integrable_of_hasCompactSupport hk
    have hθzero : (∫ x, θ x) = 0 := by
      dsimp only [θ]
      rw [integral_sub hφi (hηi.const_mul _), integral_const_mul, hηone]
      ring
    obtain ⟨ψ, hψc, hψk, hψs, hψd⟩ :=
      intervalSobolev_test_primitive hlr hθc hθk hθs hθzero
    have hzero : (∫ x, u x * θ x) = 0 := by
      have h := hu ψ hψc hψk hψs
      simpa only [hψd, zero_mul, integral_zero, neg_zero] using h
    have hupi := intervalSobolev_test_pairing_integrable hi hc.continuous hk hs
    have he : (∫ x, u x * θ x) = (∫ x, u x * φ x) - (∫ x, φ x) * c := by
      calc
        _ = ∫ x, u x * φ x - (∫ t, φ t) * (u x * η x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp only [θ]
          ring
        _ = _ := by rw [integral_sub hupi (huη.const_mul _), integral_const_mul]
    linarith
  have hz : ∀ᵐ x, x ∈ Ioo l r → u x - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hi.sub (locallyIntegrableOn_const c))
    intro φ hc hk hs
    have hup := intervalSobolev_test_pairing_integrable hi hc.continuous hk hs
    have hcp : Integrable (fun x => c * φ x) :=
      (hc.continuous.integrable_of_hasCompactSupport hk).const_mul c
    calc
      _ = ∫ x, u x * φ x - c * φ x := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [smul_eq_mul, Pi.sub_apply]
        ring
      _ = (∫ x, u x * φ x) - c * ∫ x, φ x := by
        rw [integral_sub hup hcp, integral_const_mul]
      _ = 0 := by rw [hpair φ hc hk hs]; ring
  refine ⟨c, (ae_restrict_iff' measurableSet_Ioo).mpr ?_⟩
  filter_upwards [hz] with x hx
  intro hm
  exact sub_eq_zero.mp (hx hm)

theorem IntervalWeakDerivative.sub_same {u v g : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalWeakDerivative u g l r) (hv : IntervalWeakDerivative v g l r)
    (hui : LocallyIntegrableOn u (Ioo l r)) (hvi : LocallyIntegrableOn v (Ioo l r)) :
    IntervalWeakDerivative (fun x => u x - v x) (fun _ => 0) l r := by
  intro φ hc hk hs
  have hd : Continuous (deriv φ) := hc.continuous_deriv (by simp)
  have hus := intervalSobolev_test_pairing_integrable hui hd hk.deriv
    (tsupport_deriv_subset.trans hs)
  have hvs := intervalSobolev_test_pairing_integrable hvi hd hk.deriv
    (tsupport_deriv_subset.trans hs)
  have he : (∫ x, (u x - v x) * deriv φ x) =
      (∫ x, u x * deriv φ x) - ∫ x, v x * deriv φ x := by
    simp_rw [sub_mul]
    exact integral_sub hus hvs
  rw [he, hu φ hc hk hs, hv φ hc hk hs]
  simp

end TimeTraps.Analysis
