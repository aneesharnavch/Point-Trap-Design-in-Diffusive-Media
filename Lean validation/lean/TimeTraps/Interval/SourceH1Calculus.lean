module

public import TimeTraps.Analysis.IntervalEnergy
public import TimeTraps.Analysis.SourceTransport

@[expose] public section

/-! Full H1 composition under an increasing C1 coordinate. The derivative
of the H1 function need only be integrable and square integrable. Its integral
representation, absolute continuity, and almost-everywhere chain rule are
transported using the Lebesgue change-of-variables theorem. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology

theorem source_h1_comp_integral {u φ ψ : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hc : ContinuousOn φ (Icc l r)) (hm : MonotoneOn φ (Icc l r))
    (hd : ∀ x ∈ Ioo l r, HasDerivAt φ (ψ x) x)
    (hp : ∀ x ∈ Ioo l r, 0 ≤ ψ x)
    (hu : AbsolutelyContinuousOnInterval u (φ l) (φ r)) {x : ℝ} (hx : x ∈ Icc l r) :
    (∫ t in l..x, deriv u (φ t) * ψ t) = u (φ x) - u (φ l) := by
  have hsub : uIcc l x ⊆ Icc l r := by
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2
  have hi := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := φ) (f' := ψ) (g := deriv u) (hc.mono hsub)
    (by
      intro t ht
      simp only [min_eq_left hx.1, max_eq_right hx.1] at ht
      exact hd t ⟨ht.1, ht.2.trans_le hx.2⟩)
    (by
      intro t ht
      simp only [min_eq_left hx.1, max_eq_right hx.1] at ht
      exact hp t ⟨ht.1, ht.2.trans_le hx.2⟩)
  dsimp only [Function.comp_apply] at hi
  rw [hi]
  apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
  apply hu.mono
  have hleft := hm ⟨le_rfl, hlr⟩ hx hx.1
  have hright := hm hx ⟨hlr, le_rfl⟩ hx.2
  rw [uIcc_of_le hleft, uIcc_of_le (hleft.trans hright)]
  exact Icc_subset_Icc le_rfl hright

theorem source_h1_comp {u φ ψ : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hc : ContinuousOn φ (Icc l r)) (hm : MonotoneOn φ (Icc l r))
    (hd : ∀ x ∈ Ioo l r, HasDerivAt φ (ψ x) x)
    (hψ : ContinuousOn ψ (Icc l r)) (hp : ∀ x ∈ Ioo l r, 0 ≤ ψ x)
    (hu : IntervalEnergy u (φ l) (φ r)) :
    IntervalEnergy (fun x => u (φ x)) l r ∧
      ∀ᵐ x, x ∈ Ioo l r → deriv (fun y => u (φ y)) x = deriv u (φ x) * ψ x := by
  have hcu : ContinuousOn φ (uIcc l r) := by rwa [uIcc_of_le hlr]
  have hdu : ∀ x ∈ Ioo (min l r) (max l r), HasDerivAt φ (ψ x) x := by
    simpa only [min_eq_left hlr, max_eq_right hlr] using hd
  have hpu : ∀ x ∈ Ioo (min l r) (max l r), 0 ≤ ψ x := by
    simpa only [min_eq_left hlr, max_eq_right hlr] using hp
  have hi : IntervalIntegrable (fun x => deriv u (φ x) * ψ x) volume l r :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hcu hdu hpu).mpr
      hu.absolutelyContinuous.intervalIntegrable_deriv
  have hi₂ : IntervalIntegrable (fun x => deriv u (φ x) ^ 2 * ψ x) volume l r :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hcu hdu hpu).mpr
      hu.derivative_square_integrable
  have hrep (x : ℝ) (hx : x ∈ Icc l r) :
      u (φ l) + (∫ t in l..x, deriv u (φ t) * ψ t) = u (φ x) := by
    rw [source_h1_comp_integral hlr hc hm hd hp hu.absolutelyContinuous hx]
    ring
  have ha := (interval_absolutelyContinuous_const (u (φ l)) l r).fun_add
    (hi.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : l ∈ uIcc l r))
  have hac : AbsolutelyContinuousOnInterval (fun x => u (φ x)) l r := by
    apply interval_absolutelyContinuous_congr ha
    intro x hx
    exact hrep x (by simpa only [uIcc_of_le hlr] using hx)
  have hae : ∀ᵐ x, x ∈ Ioo l r → deriv (fun y => u (φ y)) x = deriv u (φ x) * ψ x := by
    filter_upwards [hi.ae_hasDerivAt_integral] with x hx hxi
    have hdx := (hx (Icc_subset_uIcc (Ioo_subset_Icc_self hxi)) l left_mem_uIcc).const_add (u (φ l))
    have heq : (fun y => u (φ y)) =ᶠ[𝓝 x]
        (fun y => u (φ l) + ∫ t in l..y, deriv u (φ t) * ψ t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
      exact (hrep y (Ioo_subset_Icc_self hy)).symm
    exact (hdx.congr_of_eventuallyEq heq).deriv
  refine ⟨⟨hac, ?_⟩, hae⟩
  have hψu : ContinuousOn ψ (uIcc l r) := by rwa [uIcc_of_le hlr]
  have hs : IntervalIntegrable (fun x => (deriv u (φ x) * ψ x) ^ 2) volume l r := by
    apply (hi₂.mul_continuousOn hψu).congr_uIoo
    intro x _
    dsimp only
    ring
  apply hs.congr_ae
  rw [uIoc_of_le hlr]
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [hae, volume.ae_ne r] with x hx hxr hxi
  rw [hx ⟨hxi.1, lt_of_le_of_ne hxi.2 hxr⟩]

end TimeTraps.Interval
