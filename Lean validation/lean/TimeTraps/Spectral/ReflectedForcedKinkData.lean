module

public import TimeTraps.Spectral.PhysicalProblem
public import TimeTraps.Spectral.ReflectedEigenstateKinkPrimitive
public import TimeTraps.Analysis.IntervalPointForm
public import TimeTraps.Analysis.FiniteKinkCalculus

@[expose] public section

/-! A continuous-source full physical weak equation and its canonical
global C² base. The source is assumed continuous only on the closed
physical interval; its sign and differentiability are unrestricted.
The kink coefficients are the original contact reactions divided by 2D. -/

noncomputable section

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Probability
open scoped BigOperators

variable {n : ℕ}

structure WeakForcedEquation (P : SpectralProblem n) (g u : ℝ → ℝ) : Prop where
  energy : IntervalEnergy u 0 P.length
  weak_form : ∀ v : ℝ → ℝ, IntervalEnergy v 0 P.length →
    intervalPointForm P.diffusivity P.strength P.site 0 P.length u v =
      ∫ x in (0 : ℝ)..P.length, g x * v x

variable {P : SpectralProblem n} {g u : ℝ → ℝ}

def forcedKinkSource (P : SpectralProblem n) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 P.length)) : C(Icc (0 : ℝ) P.length, ℝ) :=
  ⟨fun x => g x, hg.domRestrict⟩

theorem forcedKinkSource_extension (hg : ContinuousOn g (Icc 0 P.length))
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg) x = g x :=
  reflectedFellerExtension_on_interval P.length P.length_pos (forcedKinkSource P g hg) ⟨x, hx⟩

def WeakForcedEquation.kinkBase (_hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) (z : ℝ) : ℝ :=
  (P.diffusivity * (u P.length + u 0) -
    ((P.length - z) * reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length -
      reflectedNeumannDoublePrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length +
        2 * reflectedNeumannDoublePrimitive P.length P.length_pos (forcedKinkSource P g hg) z)) /
          (2 * P.diffusivity)

def WeakForcedEquation.kinkCoefficient (_hu : WeakForcedEquation P g u) (i : Fin n) : ℝ :=
  P.strength i * u (P.site i) / (2 * P.diffusivity)

def WeakForcedEquation.kinkPotential (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) : ℝ → ℝ :=
  finiteKinkPotential (hu.kinkBase hg) Finset.univ P.site hu.kinkCoefficient

theorem WeakForcedEquation.kinkBase_contDiff (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) : ContDiff ℝ 2 (hu.kinkBase hg) := by
  have hQ := reflectedNeumannDoublePrimitive_contDiff P.length P.length_pos (forcedKinkSource P g hg)
  unfold kinkBase
  exact (contDiff_const.sub
    (((contDiff_const.sub contDiff_id).mul contDiff_const).sub contDiff_const |>.add
      (contDiff_const.mul hQ))).div_const _

theorem WeakForcedEquation.kinkBase_hasDerivAt (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) (z : ℝ) :
    HasDerivAt (hu.kinkBase hg)
      ((reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length -
        2 * reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) z) /
          (2 * P.diffusivity)) z := by
  have hQ := reflectedNeumannDoublePrimitive_derivative P.length P.length_pos (forcedKinkSource P g hg) z
  unfold kinkBase
  convert ((hasDerivAt_const z (P.diffusivity * (u P.length + u 0))).sub
    (((((hasDerivAt_const z P.length).sub (hasDerivAt_id z)).mul_const
      (reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length)).sub_const
      (reflectedNeumannDoublePrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length)).add
        (hQ.const_mul 2))).div_const (2 * P.diffusivity) using 1 <;>
    first | rfl | ring

theorem WeakForcedEquation.kinkBase_curvature (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) {z : ℝ} (hz : z ∈ Icc 0 P.length) :
    deriv (deriv (hu.kinkBase hg)) z = -g z / P.diffusivity := by
  have he : deriv (hu.kinkBase hg) = fun y =>
      (reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length -
        2 * reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) y) /
          (2 * P.diffusivity) := funext (fun y => (hu.kinkBase_hasDerivAt hg y).deriv)
  rw [he]
  have hd := ((hasDerivAt_const z
    (reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length)).sub
      ((reflectedFellerRawPrimitive_derivative P.length P.length_pos (forcedKinkSource P g hg) z).const_mul 2)).div_const
        (2 * P.diffusivity)
  dsimp only [Pi.sub_apply] at hd
  rw [hd.deriv, forcedKinkSource_extension hg hz]
  field_simp [P.diffusivity_pos.ne']
  ring

theorem WeakForcedEquation.kink_conservation (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) :
    (∑ i, P.strength i * u (P.site i)) =
      reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length := by
  have hw := hu.weak_form (fun _ => 1) (IntervalEnergy.const 1 0 P.length)
  simp only [intervalPointForm, deriv_const, mul_zero, intervalIntegral.integral_zero,
    zero_add, mul_one] at hw
  rw [hw]
  apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
  intro x hx
  exact (forcedKinkSource_extension hg (Ioo_subset_Icc_self hx)).symm

theorem WeakForcedEquation.kinkCoefficient_reaction (hu : WeakForcedEquation P g u) (i : Fin n) :
    2 * P.diffusivity * hu.kinkCoefficient i = P.strength i * u (P.site i) := by
  unfold kinkCoefficient
  field_simp [P.diffusivity_pos.ne']

theorem WeakForcedEquation.kinkCoefficient_sum (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) :
    (∑ i, hu.kinkCoefficient i) =
      reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length /
        (2 * P.diffusivity) := by
  unfold kinkCoefficient
  rw [← Finset.sum_div, hu.kink_conservation hg]

end TimeTraps.Spectral

end
