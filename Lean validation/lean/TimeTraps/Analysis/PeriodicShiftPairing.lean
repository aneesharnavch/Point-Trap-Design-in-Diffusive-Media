module

public import TimeTraps.Analysis.PeriodicShiftIntegral

@[expose] public section

/-! Periodic translation preserves the bilinear pairings for all H1 functions.
Closed-interval congruence also preserves pairings of arbitrary representatives. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem periodicShift_congr {L r : ℝ} {u v : ℝ → ℝ} (hr : r ∈ Icc 0 L)
    (h : EqOn u v (Icc 0 L)) :
    EqOn (periodicShift L r u) (periodicShift L r v) (Icc 0 L) := by
  intro x hx
  unfold periodicShift
  split
  · exact h ⟨by linarith [hr.1, hx.1], by linarith⟩
  · exact h ⟨by linarith, by linarith [hr.2, hx.2]⟩

theorem periodicShift_pos {L r : ℝ} {u : ℝ → ℝ} (hr : r ∈ Icc 0 L)
    (hu : ∀ x ∈ Icc 0 L, 0 < u x) :
    ∀ x ∈ Icc 0 L, 0 < periodicShift L r u x := by
  intro x hx
  unfold periodicShift
  split
  · exact hu _ ⟨by linarith [hr.1, hx.1], by linarith⟩
  · exact hu _ ⟨by linarith, by linarith [hr.2, hx.2]⟩

theorem periodicShift_const_mul (L r c : ℝ) (u : ℝ → ℝ) :
    periodicShift L r (fun x => c * u x) = fun x => c * periodicShift L r u x := by
  funext x
  unfold periodicShift
  split <;> rfl

theorem periodicShift_pairing {L r : ℝ} {u v : ℝ → ℝ}
    (hu : IntervalEnergy u 0 L) (hup : u 0 = u L)
    (hv : IntervalEnergy v 0 L) (hvp : v 0 = v L) (hr : r ∈ Icc 0 L) :
    (∫ x in (0 : ℝ)..L, periodicShift L r u x * periodicShift L r v x) =
      ∫ x in (0 : ℝ)..L, u x * v x := by
  apply integral_eq_of_cyclic_pieces hr (hu.continuousOn.mul hv.continuousOn).intervalIntegrable
    (((periodicShift_energy hu hup hr).continuousOn).mul
      (periodicShift_energy hv hvp hr).continuousOn).intervalIntegrable
  · intro x hx
    change periodicShift L r u x * periodicShift L r v x = u (r + x) * v (r + x)
    rw [periodicShift_left L r u hx.2.le, periodicShift_left L r v hx.2.le]
  · intro x hx
    change periodicShift L r u x * periodicShift L r v x = u (r + x - L) * v (r + x - L)
    rw [periodicShift_right hup hx.1.le, periodicShift_right hvp hx.1.le]

theorem periodicShift_derivative_pairing {L r : ℝ} {u v : ℝ → ℝ}
    (hu : IntervalEnergy u 0 L) (hup : u 0 = u L)
    (hv : IntervalEnergy v 0 L) (hvp : v 0 = v L) (hr : r ∈ Icc 0 L) :
    (∫ x in (0 : ℝ)..L, deriv (periodicShift L r u) x * deriv (periodicShift L r v) x) =
      ∫ x in (0 : ℝ)..L, deriv u x * deriv v x := by
  have hf : IntervalIntegrable (fun x => deriv u x * deriv v x) volume 0 L := by
    simpa only [one_mul] using hu.bilinear_integrable hv
      (show ContinuousOn (fun _ : ℝ => (1 : ℝ)) (uIcc 0 L) from continuousOn_const)
  have hg : IntervalIntegrable
      (fun x => deriv (periodicShift L r u) x * deriv (periodicShift L r v) x) volume 0 L := by
    simpa only [one_mul] using (periodicShift_energy hu hup hr).bilinear_integrable
      (periodicShift_energy hv hvp hr)
      (show ContinuousOn (fun _ : ℝ => (1 : ℝ)) (uIcc 0 L) from continuousOn_const)
  apply integral_eq_of_cyclic_pieces hr hf hg
  · intro x hx
    dsimp only
    rw [periodicShift_deriv_left L r u hx.2, periodicShift_deriv_left L r v hx.2]
  · intro x hx
    dsimp only
    rw [periodicShift_deriv_right L r u hx.1, periodicShift_deriv_right L r v hx.1]

theorem integral_pairing_congr_right {l r : ℝ} {u v w : ℝ → ℝ}
    (hlr : l ≤ r) (h : EqOn v w (Icc l r)) :
    (∫ x in l..r, u x * v x) = ∫ x in l..r, u x * w x := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [h (by simpa only [uIcc_of_le hlr] using hx)]

theorem integral_derivative_pairing_congr_right {l r : ℝ} {u v w : ℝ → ℝ}
    (hlr : l ≤ r) (h : EqOn v w (Icc l r)) :
    (∫ x in l..r, deriv u x * deriv v x) = ∫ x in l..r, deriv u x * deriv w x := by
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo l r := by simpa only [uIoo_of_le hlr] using hx
  dsimp only
  rw [((h.mono Ioo_subset_Icc_self).deriv isOpen_Ioo) hx']

end TimeTraps.Analysis
