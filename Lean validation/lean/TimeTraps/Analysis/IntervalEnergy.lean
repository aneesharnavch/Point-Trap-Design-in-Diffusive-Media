module

public import TimeTraps.Analysis.IntervalCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
The one-dimensional energy space, defined by absolutely continuous
representatives and square-integrable derivatives. No differential equation
or Green identity is built into membership.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

structure IntervalEnergy (u : ℝ → ℝ) (l r : ℝ) : Prop where
  absolutelyContinuous : AbsolutelyContinuousOnInterval u l r
  derivative_square_integrable : IntervalIntegrable (fun x => deriv u x ^ 2) volume l r

/-- Absolute continuity depends only on the function on its closed interval. -/
theorem interval_absolutelyContinuous_congr {u v : ℝ → ℝ} {l r : ℝ}
    (hu : AbsolutelyContinuousOnInterval u l r) (huv : EqOn u v (uIcc l r)) :
    AbsolutelyContinuousOnInterval v l r := by
  rw [absolutelyContinuousOnInterval_iff] at hu ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro I hI hlength
  have heq : (∑ i ∈ Finset.range I.1, dist (u (I.2 i).1) (u (I.2 i).2)) =
      ∑ i ∈ Finset.range I.1, dist (v (I.2 i).1) (v (I.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [huv ((hI.1 i hi).1), huv ((hI.1 i hi).2)]
  rw [← heq]
  exact hδu I hI hlength

theorem interval_absolutelyContinuous_const (c l r : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ => c) l r := by
  simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero]
  exact tendsto_const_nhds

/-- A continuous interior derivative gives the actual energy-space membership. -/
theorem intervalEnergy_of_continuous_derivative {u g : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hu : ContinuousOn u (Icc l r)) (hg : ContinuousOn g (Icc l r))
    (hd : ∀ x ∈ Ioo l r, HasDerivAt u (g x) x) : IntervalEnergy u l r := by
  have hi : IntervalIntegrable g volume l r := hg.intervalIntegrable_of_Icc hlr
  have hprimitive := hi.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : l ∈ uIcc l r)
  have hac : AbsolutelyContinuousOnInterval (fun x => u l + ∫ t in l..x, g t) l r :=
    (interval_absolutelyContinuous_const (u l) l r).fun_add hprimitive
  refine ⟨interval_absolutelyContinuous_congr hac ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Icc l r := by simpa only [uIcc_of_le hlr] using hx
    dsimp only
    rw [integral_derivative_to_point hu hg hd hx']
    ring
  · have hi₂ : IntervalIntegrable (fun x => g x ^ 2) volume l r :=
      (hg.pow 2).intervalIntegrable_of_Icc hlr
    apply hi₂.congr_uIoo
    intro x hx
    have hx' : x ∈ Ioo l r := by simpa only [uIoo_of_le hlr] using hx
    dsimp only
    rw [(hd x hx').deriv]

theorem IntervalEnergy.continuousOn {u : ℝ → ℝ} {l r : ℝ} (hu : IntervalEnergy u l r) :
    ContinuousOn u (uIcc l r) := hu.absolutelyContinuous.continuousOn

/-- The function itself is L2 on the compact interval as well as its derivative. -/
theorem IntervalEnergy.state_square_integrable {u : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) : IntervalIntegrable (fun x => u x ^ 2) volume l r :=
  (hu.continuousOn.pow 2).intervalIntegrable

theorem IntervalEnergy.const (c l r : ℝ) : IntervalEnergy (fun _ => c) l r := by
  refine ⟨interval_absolutelyContinuous_const c l r, ?_⟩
  simp

theorem IntervalEnergy.derivative_memLp {u : ℝ → ℝ} {l r : ℝ} (hu : IntervalEnergy u l r) :
    MemLp (deriv u) 2 (volume.restrict (uIoc l r)) :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_deriv u _)).mpr
    (intervalIntegrable_iff.mp hu.derivative_square_integrable)

theorem IntervalEnergy.sub {u v : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r) :
    IntervalEnergy (fun x => u x - v x) l r := by
  have hd : (fun x => deriv u x - deriv v x) =ᵐ[volume.restrict (uIoc l r)]
      deriv (fun x => u x - v x) := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hu.absolutelyContinuous.ae_differentiableAt,
      hv.absolutelyContinuous.ae_differentiableAt] with x hux hvx hx
    exact ((hux (uIoc_subset_uIcc hx)).hasDerivAt.sub
      (hvx (uIoc_subset_uIcc hx)).hasDerivAt).deriv.symm
  refine ⟨hu.absolutelyContinuous.fun_sub hv.absolutelyContinuous, ?_⟩
  apply intervalIntegrable_iff.mpr
  exact ((memLp_congr_ae hd).mp (hu.derivative_memLp.sub hv.derivative_memLp)).integrable_sq

/-- Products of energy derivatives are integrable by the L2 inequality. -/
theorem IntervalEnergy.bilinear_integrable {u v a : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (ha : ContinuousOn a (uIcc l r)) :
    IntervalIntegrable (fun x => a x * deriv u x * deriv v x) volume l r := by
  have hi : IntervalIntegrable (fun x => deriv u x * deriv v x) volume l r :=
    intervalIntegrable_iff.mpr (hu.derivative_memLp.integrable_mul hv.derivative_memLp)
  simpa only [mul_assoc] using hi.continuousOn_mul ha

theorem IntervalEnergy.weighted_square_integrable {u a : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (ha : ContinuousOn a (uIcc l r)) :
    IntervalIntegrable (fun x => a x * deriv u x ^ 2) volume l r := by
  simpa only [pow_two, mul_assoc] using hu.bilinear_integrable hu ha

/-- The energy pairing is additive under subtraction even though derivatives
of energy functions exist only almost everywhere. -/
theorem IntervalEnergy.bilinear_sub_left {u v ψ a : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (hψ : IntervalEnergy ψ l r) (ha : ContinuousOn a (uIcc l r)) :
    (∫ x in l..r, a x * deriv (fun y => u y - v y) x * deriv ψ x) =
      (∫ x in l..r, a x * deriv u x * deriv ψ x) -
      (∫ x in l..r, a x * deriv v x * deriv ψ x) := by
  rw [← intervalIntegral.integral_sub (hu.bilinear_integrable hψ ha)
    (hv.bilinear_integrable hψ ha)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hu.absolutelyContinuous.ae_differentiableAt,
    hv.absolutelyContinuous.ae_differentiableAt] with x hux hvx hx
  have hd : deriv (fun y => u y - v y) x = deriv u x - deriv v x :=
    ((hux (uIoc_subset_uIcc hx)).hasDerivAt.sub
      (hvx (uIoc_subset_uIcc hx)).hasDerivAt).deriv
  rw [hd]
  ring

/-- Zero weighted derivative energy forces an absolutely continuous function
to be constant; positivity is assumed only for the coefficient. -/
theorem IntervalEnergy.constant_of_energy_zero {u a : ℝ → ℝ} {l r : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l ≤ r) (ha : ContinuousOn a (Icc l r))
    (hapos : ∀ x ∈ Icc l r, 0 < a x)
    (hzero : (∫ x in l..r, a x * deriv u x ^ 2) = 0) :
    ∀ x ∈ Icc l r, u x = u l := by
  have hi := hu.weighted_square_integrable (by simpa only [uIcc_of_le hlr] using ha)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc l r)] (fun x => a x * deriv u x ^ 2) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun x hx =>
      mul_nonneg (hapos x ⟨hx.1.le, hx.2⟩).le (sq_nonneg _)
  have hz := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hlr hnonneg hi).mp hzero
  have hzcc : (fun x => a x * deriv u x ^ 2) =ᵐ[volume.restrict (Icc l r)] 0 := by
    rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hz
  have hderivzero : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt u 0 x := by
    have hz' := (ae_restrict_iff' measurableSet_Icc).mp hzcc
    filter_upwards [hu.absolutelyContinuous.ae_differentiableAt, hz'] with x hx hz hxmem
    have hxI : x ∈ Icc l r := by simpa only [uIcc_of_le hlr] using hxmem
    have hsq : deriv u x ^ 2 = 0 := (mul_eq_zero.mp (hz hxI)).resolve_left (ne_of_gt (hapos x hxI))
    simpa only [sq_eq_zero_iff.mp hsq] using (hx hxmem).hasDerivAt
  obtain ⟨c, hc⟩ := hu.absolutelyContinuous.const_of_ae_hasDerivAt_zero hderivzero
  intro x hx
  exact (hc x (by simpa only [uIcc_of_le hlr] using hx)).trans (hc l left_mem_uIcc).symm

end TimeTraps.Analysis
