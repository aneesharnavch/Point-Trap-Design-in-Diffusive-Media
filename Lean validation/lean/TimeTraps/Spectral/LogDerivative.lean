module

public import TimeTraps.Analysis.IntervalEnergy
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
The logarithmic derivative of a positive gap eigenfunction satisfies the
Riccati equation. Its absolute continuity supplies the exact ground-state
square identity for arbitrary H1 test functions.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology

theorem logarithmic_derivative {u g : ℝ → ℝ} {a x : ℝ}
    (hu : u x ≠ 0) (hdu : HasDerivAt u (g x) x) (hdg : HasDerivAt g (-a * u x) x) :
    HasDerivAt (fun t => g t / u t) (-a - (g x / u x) ^ 2) x := by
  have h := hdg.div hdu hu
  have he : ((-a * u x) * u x - g x * g x) / (u x) ^ 2 = -a - (g x / u x) ^ 2 := by
    field_simp
  rwa [he] at h

theorem logarithmic_energy {u g : ℝ → ℝ} {a l r : ℝ} (hlr : l ≤ r)
    (hu : ContinuousOn u (Icc l r)) (hg : ContinuousOn g (Icc l r))
    (hpos : ∀ x ∈ Icc l r, 0 < u x)
    (hdu : ∀ x ∈ Ioo l r, HasDerivAt u (g x) x)
    (hdg : ∀ x ∈ Ioo l r, HasDerivAt g (-a * u x) x) :
    IntervalEnergy (fun t => g t / u t) l r := by
  have hq := hg.div hu (fun x hx => ne_of_gt (hpos x hx))
  exact intervalEnergy_of_continuous_derivative hlr hq (continuousOn_const.sub (hq.pow 2))
    (fun x hx => logarithmic_derivative (ne_of_gt (hpos x (Ioo_subset_Icc_self hx))) (hdu x hx) (hdg x hx))

theorem shifted_square_integrable {v q : ℝ → ℝ} {l r : ℝ}
    (hv : IntervalEnergy v l r) (hq : ContinuousOn q (uIcc l r)) :
    IntervalIntegrable (fun x => (deriv v x - q x * v x) ^ 2) volume l r := by
  have hcross := hv.absolutelyContinuous.intervalIntegrable_deriv.mul_continuousOn (hq.mul hv.continuousOn)
  have hlast : IntervalIntegrable (fun x => (q x * v x) ^ 2) volume l r :=
    ((hq.mul hv.continuousOn).pow 2).intervalIntegrable
  have hi := (hv.derivative_square_integrable.sub (hcross.const_mul 2)).add hlast
  apply hi.congr
  intro x _
  simp only [Pi.mul_apply]
  ring

theorem riccati_square_identity {v q : ℝ → ℝ} {a l r : ℝ} (hlr : l ≤ r)
    (hv : IntervalEnergy v l r) (hq : ContinuousOn q (Icc l r))
    (hdq : ∀ x ∈ Ioo l r, HasDerivAt q (-a - q x ^ 2) x) :
    (∫ x in l..r, deriv v x ^ 2) - a * (∫ x in l..r, v x ^ 2) =
      (∫ x in l..r, (deriv v x - q x * v x) ^ 2) + q r * v r ^ 2 - q l * v l ^ 2 := by
  have hqe := intervalEnergy_of_continuous_derivative hlr hq
    (continuousOn_const.sub (hq.pow 2)) hdq
  have hprod := hqe.absolutelyContinuous.integral_deriv_mul_eq_sub
    (hv.absolutelyContinuous.fun_mul hv.absolutelyContinuous)
  have he : (∫ x in l..r, deriv v x ^ 2 - a * v x ^ 2 - (deriv v x - q x * v x) ^ 2) =
      ∫ x in l..r, deriv q x * (v x * v x) + q x * deriv (fun t => v t * v t) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hv.absolutelyContinuous.ae_differentiableAt, volume.ae_ne r] with x hdx hxr hx
    have hxcc : x ∈ uIcc l r := uIoc_subset_uIcc hx
    have hxoc : x ∈ Ioc l r := by simpa only [uIoc_of_le hlr] using hx
    have hxoo : x ∈ Ioo l r := ⟨hxoc.1, lt_of_le_of_ne hxoc.2 hxr⟩
    have hdv := (hdx hxcc).hasDerivAt.mul (hdx hxcc).hasDerivAt
    change HasDerivAt (fun t => v t * v t) (deriv v x * v x + v x * deriv v x) x at hdv
    rw [(hdq x hxoo).deriv, hdv.deriv]
    ring
  rw [hprod] at he
  have hmass := hv.state_square_integrable.const_mul a
  have hshift := shifted_square_integrable hv (by simpa only [uIcc_of_le hlr] using hq)
  rw [intervalIntegral.integral_sub (hv.derivative_square_integrable.sub hmass) hshift,
    intervalIntegral.integral_sub hv.derivative_square_integrable hmass,
    intervalIntegral.integral_const_mul] at he
  nlinarith

end TimeTraps.Spectral
