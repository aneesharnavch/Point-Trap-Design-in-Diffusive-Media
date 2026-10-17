module

public import TimeTraps.Spectral.DirichletRayleigh
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-!
Polarization in the actual signed H1 admissible space. Every minimizer of
the independent Dirichlet Rayleigh problem satisfies its full weak equation;
no differentiability of the competitor or positivity of its values is added.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology

theorem dirichlet_variation_energy {u v : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r) (t : ℝ) :
    IntervalEnergy (fun x => u x + t * v x) l r := by
  have he : (fun x => deriv u x + t * deriv v x) =ᵐ[volume.restrict (uIoc l r)]
      deriv (fun x => u x + t * v x) := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hu.absolutelyContinuous.ae_differentiableAt,
      hv.absolutelyContinuous.ae_differentiableAt] with x hux hvx hx
    exact ((hux (uIoc_subset_uIcc hx)).hasDerivAt.add
      ((hvx (uIoc_subset_uIcc hx)).hasDerivAt.const_mul t)).deriv.symm
  refine ⟨hu.absolutelyContinuous.fun_add
    ((interval_absolutelyContinuous_const t l r).fun_mul hv.absolutelyContinuous), ?_⟩
  apply intervalIntegrable_iff.mpr
  exact ((memLp_congr_ae he).mp
    (hu.derivative_memLp.add (hv.derivative_memLp.const_mul t))).integrable_sq

theorem DirichletInterval.admissible_variation (P : DirichletInterval) {u v : ℝ → ℝ}
    (hu : P.admissible u) (hv : P.admissible v) (t : ℝ) :
    P.admissible (fun x => u x + t * v x) := by
  refine ⟨dirichlet_variation_energy hu.1 hv.1 t, ?_⟩
  have htu := hu.2
  have htv := hv.2
  cases he : P.ends <;> simp_all [zeroTraces]

theorem dirichlet_integral_square_variation {f g : ℝ → ℝ} {l r : ℝ}
    (hf : IntervalIntegrable (fun x => f x ^ 2) volume l r)
    (hg : IntervalIntegrable (fun x => g x ^ 2) volume l r)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume l r) (t : ℝ) :
    (∫ x in l..r, (f x + t * g x) ^ 2) =
      (∫ x in l..r, f x ^ 2) + 2 * t * (∫ x in l..r, f x * g x) +
        t ^ 2 * (∫ x in l..r, g x ^ 2) := by
  have he : (fun x => (f x + t * g x) ^ 2) =
      fun x => (f x ^ 2 + 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2 := by
    funext x
    ring
  rw [he, intervalIntegral.integral_add (hf.add (hfg.const_mul (2 * t)))
    (hg.const_mul (t ^ 2)), intervalIntegral.integral_add hf (hfg.const_mul (2 * t))]
  simp only [intervalIntegral.integral_const_mul]

theorem DirichletInterval.quadraticForm_variation (P : DirichletInterval) {u v : ℝ → ℝ}
    (hu : P.admissible u) (hv : P.admissible v) (t : ℝ) :
    P.quadraticForm (fun x => u x + t * v x) = P.quadraticForm u +
      2 * t * (P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x)) +
        t ^ 2 * P.quadraticForm v := by
  have he : (∫ x in (0 : ℝ)..P.length, deriv (fun y => u y + t * v y) x ^ 2) =
      ∫ x in (0 : ℝ)..P.length, (deriv u x + t * deriv v x) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hu.1.absolutelyContinuous.ae_differentiableAt,
      hv.1.absolutelyContinuous.ae_differentiableAt] with x hux hvx hx
    have hd := ((hux (uIoc_subset_uIcc hx)).hasDerivAt.add
      ((hvx (uIoc_subset_uIcc hx)).hasDerivAt.const_mul t)).deriv
    change deriv (fun y => u y + t * v y) x = deriv u x + t * deriv v x at hd
    rw [hd]
  have hcross : IntervalIntegrable (fun x => deriv u x * deriv v x) volume 0 P.length := by
    simpa only [one_mul] using hu.1.bilinear_integrable hv.1
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (uIcc 0 P.length))
  unfold quadraticForm
  rw [he, dirichlet_integral_square_variation hu.1.derivative_square_integrable
    hv.1.derivative_square_integrable hcross t]
  ring

theorem DirichletInterval.squareMass_variation (P : DirichletInterval) {u v : ℝ → ℝ}
    (hu : P.admissible u) (hv : P.admissible v) (t : ℝ) :
    P.squareMass (fun x => u x + t * v x) = P.squareMass u +
      2 * t * (∫ x in (0 : ℝ)..P.length, u x * v x) + t ^ 2 * P.squareMass v :=
  dirichlet_integral_square_variation hu.1.state_square_integrable hv.1.state_square_integrable
    (hu.1.continuousOn.mul hv.1.continuousOn).intervalIntegrable t

theorem DirichletInterval.weak_of_quadraticForm_eq (P : DirichletInterval) {u : ℝ → ℝ}
    (hu : P.admissible u) (heq : P.quadraticForm u = P.principalValue * P.squareMass u) :
    DirichletWeakEigenEquation P P.principalValue u := by
  refine ⟨hu, ?_⟩
  intro v hv
  let b := P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) -
    P.principalValue * (∫ x in (0 : ℝ)..P.length, u x * v x)
  let c := P.quadraticForm v - P.principalValue * P.squareMass v
  let f := fun t : ℝ => 2 * t * b + t ^ 2 * c
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := P.quadraticForm_lower (P.admissible_variation hu hv t)
    rw [← P.principalValue_eq, P.quadraticForm_variation hu hv,
      P.squareMass_variation hu hv, heq] at h
    change f 0 ≤ f t
    dsimp [f, b, c]
    nlinarith
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const b).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const c)
  have hz := hmin.hasDerivAt_eq_zero hd
  norm_num at hz
  dsimp [b] at hz
  linarith

theorem DirichletInterval.weak_of_rayleigh_minimizer (P : DirichletInterval) {u : ℝ → ℝ}
    (hu : P.admissible u) (hm : 0 < P.squareMass u)
    (heq : P.quadraticForm u / P.squareMass u = P.principalValue) :
    DirichletWeakEigenEquation P P.principalValue u :=
  P.weak_of_quadraticForm_eq hu ((div_eq_iff hm.ne').mp heq)

end TimeTraps.Spectral
