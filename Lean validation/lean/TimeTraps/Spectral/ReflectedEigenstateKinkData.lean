module

public import TimeTraps.Spectral.WeakEigenstate
public import TimeTraps.Spectral.ReflectedEigenstateKinkPrimitive
public import TimeTraps.Analysis.FiniteKinkCalculus

@[expose] public section

/-! Canonical globally C² base and signed kink coefficients for any full
physical weak eigenstate. No sign, nonvanishing, or smoothness assumption is
placed on the eigenstate beyond its original H¹ weak equation. -/

noncomputable section

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Probability
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ} {u : ℝ → ℝ}

def WeakEigenEquation.kinkProfile (hu : WeakEigenEquation P ev u) :
    C(Icc (0 : ℝ) P.length, ℝ) where
  toFun x := u x
  continuous_toFun := by
    have hc := hu.energy.continuousOn
    rw [uIcc_of_le P.length_pos.le] at hc
    exact continuousOn_iff_continuous_domRestrict.mp hc

theorem WeakEigenEquation.kinkProfile_extension (hu : WeakEigenEquation P ev u)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    reflectedFellerExtension P.length P.length_pos hu.kinkProfile x = u x :=
  reflectedFellerExtension_on_interval P.length P.length_pos hu.kinkProfile ⟨x, hx⟩

def WeakEigenEquation.kinkBase (hu : WeakEigenEquation P ev u) (z : ℝ) : ℝ :=
  (P.diffusivity * (u P.length + u 0) - ev *
    ((P.length - z) * reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile P.length -
      reflectedNeumannDoublePrimitive P.length P.length_pos hu.kinkProfile P.length +
        2 * reflectedNeumannDoublePrimitive P.length P.length_pos hu.kinkProfile z)) / (2 * P.diffusivity)

def WeakEigenEquation.kinkCoefficient (_hu : WeakEigenEquation P ev u) (i : Fin n) : ℝ :=
  P.strength i * u (P.site i) / (2 * P.diffusivity)

def WeakEigenEquation.kinkPotential (hu : WeakEigenEquation P ev u) : ℝ → ℝ :=
  finiteKinkPotential hu.kinkBase Finset.univ P.site hu.kinkCoefficient

theorem WeakEigenEquation.kinkBase_contDiff (hu : WeakEigenEquation P ev u) :
    ContDiff ℝ 2 hu.kinkBase := by
  have hQ := reflectedNeumannDoublePrimitive_contDiff P.length P.length_pos hu.kinkProfile
  unfold kinkBase
  exact (contDiff_const.sub (contDiff_const.mul
    (((contDiff_const.sub contDiff_id).mul contDiff_const).sub contDiff_const |>.add
      (contDiff_const.mul hQ)))).div_const _

theorem WeakEigenEquation.kinkBase_hasDerivAt (hu : WeakEigenEquation P ev u) (z : ℝ) :
    HasDerivAt hu.kinkBase
      (ev * (reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile P.length -
        2 * reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile z) / (2 * P.diffusivity)) z := by
  have hQ := reflectedNeumannDoublePrimitive_derivative P.length P.length_pos hu.kinkProfile z
  unfold kinkBase
  convert ((hasDerivAt_const z (P.diffusivity * (u P.length + u 0))).sub
    (((((hasDerivAt_const z P.length).sub (hasDerivAt_id z)).mul_const
      (reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile P.length)).sub_const
      (reflectedNeumannDoublePrimitive P.length P.length_pos hu.kinkProfile P.length)).add
        (hQ.const_mul 2) |>.const_mul ev)).div_const (2 * P.diffusivity) using 1 <;>
    first | rfl | ring

theorem WeakEigenEquation.kinkBase_curvature (hu : WeakEigenEquation P ev u)
    {z : ℝ} (hz : z ∈ Icc 0 P.length) :
    deriv (deriv hu.kinkBase) z = -ev * u z / P.diffusivity := by
  have he : deriv hu.kinkBase = fun y =>
      ev * (reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile P.length -
        2 * reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile y) / (2 * P.diffusivity) :=
    funext (fun y => (hu.kinkBase_hasDerivAt y).deriv)
  rw [he]
  have hd := (((hasDerivAt_const z
    (reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile P.length)).sub
      ((reflectedFellerRawPrimitive_derivative P.length P.length_pos hu.kinkProfile z).const_mul 2)).const_mul ev).div_const
        (2 * P.diffusivity)
  dsimp only [Pi.sub_apply] at hd
  rw [hd.deriv, hu.kinkProfile_extension hz]
  field_simp [P.diffusivity_pos.ne']
  ring

theorem WeakEigenEquation.kink_conservation (hu : WeakEigenEquation P ev u) :
    (∑ i, P.strength i * u (P.site i)) =
      ev * reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile P.length := by
  have hw := hu.weak_form (fun _ => 1) (IntervalEnergy.const 1 0 P.length)
  simp only [deriv_const, mul_zero, intervalIntegral.integral_zero, zero_add, mul_one] at hw
  rw [hw]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
  intro x hx
  exact (hu.kinkProfile_extension (Ioo_subset_Icc_self hx)).symm

theorem WeakEigenEquation.kinkCoefficient_reaction (hu : WeakEigenEquation P ev u) (i : Fin n) :
    2 * P.diffusivity * hu.kinkCoefficient i = P.strength i * u (P.site i) := by
  unfold kinkCoefficient
  field_simp [P.diffusivity_pos.ne']

theorem WeakEigenEquation.kinkCoefficient_sum (hu : WeakEigenEquation P ev u) :
    (∑ i, hu.kinkCoefficient i) =
      ev * reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile P.length / (2 * P.diffusivity) := by
  unfold kinkCoefficient
  rw [← Finset.sum_div, hu.kink_conservation]

end TimeTraps.Spectral

end
