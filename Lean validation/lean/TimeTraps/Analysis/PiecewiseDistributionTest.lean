module

public import TimeTraps.Analysis.PiecewiseDistributionCalculus

@[expose] public section

/-! The full distributional second-derivative test identity for a continuous
function on a finite ordered partition. Classical derivatives are prescribed
only inside pieces; finite one-sided slope traces and integrable second
derivatives are explicit regularity assumptions. No reaction law or sign
restriction is imposed on a slope jump. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology ContDiff Distributions

structure PiecewiseDerivativeData {n : ℕ} (q : Fin (n + 2) → ℝ) (u : ℝ → ℝ)
    (j g : Fin (n + 1) → ℝ → ℝ) : Prop where
  node_strictMono : StrictMono q
  state_continuous : ContinuousOn u (Icc (q 0) (q (Fin.last (n + 1))))
  slope_continuous : ∀ e, ContinuousOn (j e) (Icc (q e.castSucc) (q e.succ))
  density_integrable : ∀ e, IntervalIntegrable (g e) volume (q e.castSucc) (q e.succ)
  state_derivative : ∀ e x, x ∈ Ioo (q e.castSucc) (q e.succ) → HasDerivAt u (j e x) x
  slope_derivative : ∀ e x, x ∈ Ioo (q e.castSucc) (q e.succ) → HasDerivAt (j e) (g e x) x

def piecewiseSlopeJump {n : ℕ} (q : Fin (n + 2) → ℝ) (j : Fin (n + 1) → ℝ → ℝ)
    (i : Fin n) : ℝ :=
  j i.succ (q i.castSucc.succ) - j i.castSucc (q i.castSucc.succ)

theorem PiecewiseDerivativeData.classical_second {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g)
    (e : Fin (n + 1)) (x : ℝ) (hx : x ∈ Ioo (q e.castSucc) (q e.succ)) :
    deriv (deriv u) x = g e x := by
  have he : deriv u =ᶠ[𝓝 x] j e := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (h.state_derivative e y hy).deriv
  exact he.deriv_eq.trans (h.slope_derivative e x hx).deriv

theorem PiecewiseDerivativeData.slope_trace {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g)
    (e : Fin (n + 1)) (x : ℝ) (hx : x ∈ Icc (q e.castSucc) (q e.succ)) :
    Tendsto (deriv u) (𝓝[Ioo (q e.castSucc) (q e.succ)] x) (𝓝 (j e x)) := by
  have he : deriv u =ᶠ[𝓝[Ioo (q e.castSucc) (q e.succ)] x] j e := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (h.state_derivative e y hy).deriv
  exact ((h.slope_continuous e x hx).mono Ioo_subset_Icc_self).congr' he.symm

theorem PiecewiseDerivativeData.second_green {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    (∫ x in q 0..q (Fin.last (n + 1)), u x * deriv (deriv φ) x) =
      (∑ e : Fin (n + 1), ∫ x in q e.castSucc..q e.succ, g e x * φ x) +
      u (q (Fin.last (n + 1))) * deriv φ (q (Fin.last (n + 1))) - u (q 0) * deriv φ (q 0) -
      j (Fin.last n) (q (Fin.last (n + 1))) * φ (q (Fin.last (n + 1))) + j 0 (q 0) * φ (q 0) +
      ∑ i : Fin n, piecewiseSlopeJump q j i * φ (q i.castSucc.succ) := by
  have hq := h.node_strictMono.monotone
  have hφd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hi : IntervalIntegrable (fun x => u x * deriv (deriv φ) x) volume
      (q 0) (q (Fin.last (n + 1))) :=
    (h.state_continuous.mul (hφd.continuous_deriv (by simp)).continuousOn).intervalIntegrable_of_Icc
      (hq (Fin.zero_le _))
  have hu (e : Fin (n + 1)) : ContinuousOn u (Icc (q e.castSucc) (q e.succ)) :=
    h.state_continuous.mono (Icc_subset_Icc (hq (Fin.zero_le _)) (hq (Fin.le_last _)))
  have he (e : Fin (n + 1)) :
      (∫ x in q e.castSucc..q e.succ, u x * deriv (deriv φ) x) =
        (∫ x in q e.castSucc..q e.succ, g e x * φ x) +
        (u (q e.succ) * deriv φ (q e.succ) - u (q e.castSucc) * deriv φ (q e.castSucc)) +
        (j e (q e.castSucc) * φ (q e.castSucc) - j e (q e.succ) * φ (q e.succ)) := by
    have he := piecewise_edge_second_green (h.node_strictMono Fin.castSucc_lt_succ).le
      (hu e) (h.slope_continuous e) (h.density_integrable e)
      (h.state_derivative e) (h.slope_derivative e) hφ
    linarith
  rw [← piecewise_integral_sum q hq _ hi]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    piecewise_adjacent_sum (fun v => u (q v) * deriv φ (q v)),
    piecewise_boundary_sum (fun e => j e (q e.castSucc) * φ (q e.castSucc))
      (fun e => j e (q e.succ) * φ (q e.succ))]
  have hjump : (∑ i : Fin n, (j i.succ (q i.succ.castSucc) * φ (q i.succ.castSucc) -
      j i.castSucc (q i.castSucc.succ) * φ (q i.castSucc.succ))) =
      ∑ i : Fin n, piecewiseSlopeJump q j i * φ (q i.castSucc.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [piecewiseSlopeJump, Fin.succ_castSucc]
    ring
  rw [hjump]
  simp only [Fin.castSucc_zero, Fin.succ_last]
  ring

theorem PiecewiseDerivativeData.test_identity {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (_hk : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (q 0) (q (Fin.last (n + 1)))) :
    (∫ x, u x * deriv (deriv φ) x) =
      (∑ e : Fin (n + 1), ∫ x in q e.castSucc..q e.succ, g e x * φ x) +
      ∑ i : Fin n, piecewiseSlopeJump q j i * φ (q i.castSucc.succ) := by
  have hz (f : ℝ → ℝ) (hf : tsupport f ⊆ Ioo (q 0) (q (Fin.last (n + 1)))) :
      f (q 0) = 0 ∧ f (q (Fin.last (n + 1))) = 0 := by
    constructor
    · by_contra hn
      exact (lt_irrefl _) (hf (subset_closure hn)).1
    · by_contra hn
      exact (lt_irrefl _) (hf (subset_closure hn)).2
  have hφz := hz φ hs
  have hφdz := hz (deriv φ) (tsupport_deriv_subset.trans hs)
  have hi := h.second_green φ hφ
  rw [hφz.1, hφz.2, hφdz.1, hφdz.2] at hi
  simp only [mul_zero, add_zero, sub_zero] at hi
  rw [intervalSobolev_test_integral (h.node_strictMono.monotone (Fin.zero_le _))
    (tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hs))] at hi
  exact hi

theorem PiecewiseDerivativeData.testFunction_identity {n : ℕ} {q : Fin (n + 2) → ℝ}
    {u : ℝ → ℝ} {j g : Fin (n + 1) → ℝ → ℝ} (h : PiecewiseDerivativeData q u j g)
    (φ : 𝓓(⟨Ioo (q 0) (q (Fin.last (n + 1))), isOpen_Ioo⟩, ℝ)) :
    (∫ x, u x * deriv (deriv φ) x) =
      (∑ e : Fin (n + 1), ∫ x in q e.castSucc..q e.succ, g e x * φ x) +
      ∑ i : Fin n, piecewiseSlopeJump q j i * φ (q i.castSucc.succ) :=
  h.test_identity φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset

end TimeTraps.Analysis
