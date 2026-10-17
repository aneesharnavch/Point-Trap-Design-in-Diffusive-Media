module

public import TimeTraps.Analysis.IntervalEnergy
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

/-! Polynomial approximation with exact endpoint values. Correcting the
two traces by affine interpolation preserves uniform approximation and
gives actual H1 functions, for arbitrary continuous interval data. -/

namespace TimeTraps.Analysis

open Set Polynomial
open scoped Polynomial

noncomputable def endpointCorrectedPolynomial (L a b : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p + C (a - p.eval 0) * (1 - C L⁻¹ * X) + C (b - p.eval L) * C L⁻¹ * X

theorem endpointCorrectedPolynomial_eval (L a b : ℝ) (p : ℝ[X]) (x : ℝ) :
    (endpointCorrectedPolynomial L a b p).eval x =
      p.eval x + (a - p.eval 0) * (1 - L⁻¹ * x) + (b - p.eval L) * (L⁻¹ * x) := by
  simp only [endpointCorrectedPolynomial, eval_add, eval_mul, eval_C, eval_sub, eval_one,
    eval_X, mul_assoc]

theorem endpointCorrectedPolynomial_endpoints {L : ℝ} (hL : 0 < L) (a b : ℝ) (p : ℝ[X]) :
    (endpointCorrectedPolynomial L a b p).eval 0 = a ∧
      (endpointCorrectedPolynomial L a b p).eval L = b := by
  constructor
  · rw [endpointCorrectedPolynomial_eval]
    ring
  · rw [endpointCorrectedPolynomial_eval, inv_mul_cancel₀ hL.ne']
    ring

theorem polynomial_intervalEnergy (p : ℝ[X]) {l r : ℝ} (hlr : l ≤ r) :
    IntervalEnergy (fun x => p.eval x) l r :=
  intervalEnergy_of_continuous_derivative hlr p.continuous.continuousOn
    p.derivative.continuous.continuousOn (fun x _ => p.hasDerivAt x)

theorem endpointCorrectedPolynomial_error {L : ℝ} (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) (p : ℝ[X]) {δ : ℝ}
    (hp : ∀ x : Icc (0 : ℝ) L, |p.eval x.val - f x| < δ)
    (x : Icc (0 : ℝ) L) :
    |(endpointCorrectedPolynomial L (f ⟨0, le_rfl, hL.le⟩)
      (f ⟨L, hL.le, le_rfl⟩) p).eval x.val - f x| < 3 * δ := by
  let a := f ⟨0, le_rfl, hL.le⟩
  let b := f ⟨L, hL.le, le_rfl⟩
  have h0 : |a - p.eval 0| < δ := by
    simpa only [abs_sub_comm] using hp ⟨0, le_rfl, hL.le⟩
  have h1 : |b - p.eval L| < δ := by
    simpa only [abs_sub_comm] using hp ⟨L, hL.le, le_rfl⟩
  have hr0 : 0 ≤ L⁻¹ * x.val := mul_nonneg (inv_nonneg.mpr hL.le) x.property.1
  have hr1 : L⁻¹ * x.val ≤ 1 := by
    calc
      _ ≤ L⁻¹ * L := mul_le_mul_of_nonneg_left x.property.2 (inv_nonneg.mpr hL.le)
      _ = 1 := inv_mul_cancel₀ hL.ne'
  have hc0 : |(a - p.eval 0) * (1 - L⁻¹ * x.val)| ≤ |a - p.eval 0| := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hr1)]
    nlinarith [abs_nonneg (a - p.eval 0)]
  have hc1 : |(b - p.eval L) * (L⁻¹ * x.val)| ≤ |b - p.eval L| := by
    rw [abs_mul, abs_of_nonneg hr0]
    nlinarith [abs_nonneg (b - p.eval L)]
  rw [endpointCorrectedPolynomial_eval]
  change |p.eval x.val + (a - p.eval 0) * (1 - L⁻¹ * x.val) +
    (b - p.eval L) * (L⁻¹ * x.val) - f x| < _
  have he : p.eval x.val + (a - p.eval 0) * (1 - L⁻¹ * x.val) +
      (b - p.eval L) * (L⁻¹ * x.val) - f x =
      (p.eval x.val - f x + (a - p.eval 0) * (1 - L⁻¹ * x.val)) +
        (b - p.eval L) * (L⁻¹ * x.val) := by ring
  rw [he]
  have ha := abs_add_le (p.eval x.val - f x) ((a - p.eval 0) * (1 - L⁻¹ * x.val))
  have hb := abs_add_le (p.eval x.val - f x + (a - p.eval 0) * (1 - L⁻¹ * x.val))
    ((b - p.eval L) * (L⁻¹ * x.val))
  linarith [hp x]

theorem endpoint_polynomial_approximation {L : ℝ} (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], p.eval 0 = f ⟨0, le_rfl, hL.le⟩ ∧
      p.eval L = f ⟨L, hL.le, le_rfl⟩ ∧
        ∀ x : Icc (0 : ℝ) L, |p.eval x.val - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 L f (ε / 4) (by positivity)
  have hpoint : ∀ x : Icc (0 : ℝ) L, |p.eval x.val - f x| < ε / 4 := by
    intro x
    exact (ContinuousMap.norm_coe_le_norm (p.toContinuousMapOn (Icc 0 L) - f) x).trans_lt hp
  let q := endpointCorrectedPolynomial L (f ⟨0, le_rfl, hL.le⟩) (f ⟨L, hL.le, le_rfl⟩) p
  refine ⟨q, (endpointCorrectedPolynomial_endpoints hL _ _ p).1,
    (endpointCorrectedPolynomial_endpoints hL _ _ p).2, fun x => ?_⟩
  exact (endpointCorrectedPolynomial_error hL f p hpoint x).trans (by linarith)

end TimeTraps.Analysis
