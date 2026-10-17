module

public import TimeTraps.Analysis.IntervalSobolevSpaceRepresentation

@[expose] public section

/-! The bundled L2 pairings and Hilbert inner product agree with the
actual interval integrals of the unique energy representatives. Every
bundled element is recovered by embedding its representative. -/

namespace TimeTraps.Analysis.IntervalSobolevSpace

open Set MeasureTheory Filter
open scoped InnerProductSpace

theorem state_inner {l r : ℝ} (u v : IntervalSobolevSpace l r) (hlr : l < r) :
    ⟪u.state, v.state⟫_ℝ =
      ∫ x in l..r, u.representative hlr x * v.representative hlr x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [(u.representative_spec hlr).2.1,
    (v.representative_spec hlr).2.1] with x hx hy
  simp only [Real.inner_apply, hx, hy]

theorem gradient_inner {l r : ℝ} (u v : IntervalSobolevSpace l r) (hlr : l < r) :
    ⟪u.gradient, v.gradient⟫_ℝ =
      ∫ x in l..r, deriv (u.representative hlr) x * deriv (v.representative hlr) x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [(u.representative_spec hlr).2.2,
    (v.representative_spec hlr).2.2] with x hx hy
  simp only [Real.inner_apply, hx, hy]

theorem inner_eq {l r : ℝ} (u v : IntervalSobolevSpace l r) (hlr : l < r) :
    ⟪u, v⟫_ℝ = (∫ x in l..r, u.representative hlr x * v.representative hlr x) +
      ∫ x in l..r, deriv (u.representative hlr) x * deriv (v.representative hlr) x := by
  change ⟪u.state, v.state⟫_ℝ + ⟪u.gradient, v.gradient⟫_ℝ = _
  rw [state_inner u v hlr, gradient_inner u v hlr]

theorem ofEnergy_representative {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r) :
    ofEnergy (u.representative_spec hlr).1 hlr = u := by
  apply ext_state
  apply Lp.ext
  exact (ofEnergy_spec (u.representative_spec hlr).1 hlr).1.trans
    (u.representative_spec hlr).2.1.symm

end TimeTraps.Analysis.IntervalSobolevSpace
