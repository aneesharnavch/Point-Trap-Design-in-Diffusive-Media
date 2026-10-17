module

public import TimeTraps.Spectral.ReflectedEigenstateKinkPrimitive
public import TimeTraps.Analysis.FiniteKinkCalculus
public import TimeTraps.Analysis.ReflectedMeanKinkGreen

@[expose] public section

/-! The full physical Robin equation with continuous signed source.
Every H1 test is admitted. The finite interior label family may be empty,
and no positivity, ordering or uniqueness assumption is hidden in this
analytic record. The global C2 base retains both endpoint reactions. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

structure ReflectedRobinWeakEquation (L D : ℝ) (a κ : ι → ℝ) (β₀ βL : ℝ)
    (g u : ℝ → ℝ) : Prop where
  energy : IntervalEnergy u 0 L
  weak_form : ∀ v : ℝ → ℝ, IntervalEnergy v 0 L →
    D * (∫ x in (0 : ℝ)..L, deriv u x * deriv v x) +
      (∑ i, κ i * u (a i) * v (a i)) + β₀ * u 0 * v 0 + βL * u L * v L =
        ∫ x in (0 : ℝ)..L, g x * v x

variable {L D : ℝ} {a κ : ι → ℝ} {β₀ βL : ℝ} {g u : ℝ → ℝ}

def reflectedRobinKinkSource (L : ℝ) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 L)) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun x => g x, hg.domRestrict⟩

theorem reflectedRobinKinkSource_extension (hL : 0 < L) (hg : ContinuousOn g (Icc 0 L))
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg) x = g x :=
  reflectedFellerExtension_on_interval L hL (reflectedRobinKinkSource L g hg) ⟨x, hx⟩

def ReflectedRobinWeakEquation.kinkBase (_hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hg : ContinuousOn g (Icc 0 L)) (z : ℝ) : ℝ :=
  (D * (u L + u 0) + β₀ * u 0 * z + βL * u L * (L - z) -
    ((L - z) * reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) L -
      reflectedNeumannDoublePrimitive L hL (reflectedRobinKinkSource L g hg) L +
        2 * reflectedNeumannDoublePrimitive L hL (reflectedRobinKinkSource L g hg) z)) / (2 * D)

def ReflectedRobinWeakEquation.kinkCoefficient (_hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (i : ι) : ℝ := κ i * u (a i) / (2 * D)

def ReflectedRobinWeakEquation.kinkPotential (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hg : ContinuousOn g (Icc 0 L)) : ℝ → ℝ :=
  finiteKinkPotential (hu.kinkBase hL hg) Finset.univ a hu.kinkCoefficient

theorem ReflectedRobinWeakEquation.kinkBase_contDiff (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hg : ContinuousOn g (Icc 0 L)) : ContDiff ℝ 2 (hu.kinkBase hL hg) := by
  have hQ := reflectedNeumannDoublePrimitive_contDiff L hL (reflectedRobinKinkSource L g hg)
  unfold kinkBase
  fun_prop

theorem ReflectedRobinWeakEquation.kinkBase_hasDerivAt (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hg : ContinuousOn g (Icc 0 L)) (z : ℝ) :
    HasDerivAt (hu.kinkBase hL hg)
      ((β₀ * u 0 - βL * u L + reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) L -
        2 * reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) z) / (2 * D)) z := by
  have hQ := reflectedNeumannDoublePrimitive_derivative L hL (reflectedRobinKinkSource L g hg) z
  unfold kinkBase
  convert! ((((hasDerivAt_const z (D * (u L + u 0))).add
    ((hasDerivAt_id z).const_mul (β₀ * u 0))).add
      (((hasDerivAt_const z L).sub (hasDerivAt_id z)).const_mul (βL * u L))).sub
    (((((hasDerivAt_const z L).sub (hasDerivAt_id z)).mul_const
      (reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) L)).sub_const
      (reflectedNeumannDoublePrimitive L hL (reflectedRobinKinkSource L g hg) L)).add
        (hQ.const_mul 2))).div_const (2 * D) using 1
  ring

theorem ReflectedRobinWeakEquation.kinkBase_curvature (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (hg : ContinuousOn g (Icc 0 L)) {z : ℝ} (hz : z ∈ Icc 0 L) :
    deriv (deriv (hu.kinkBase hL hg)) z = -g z / D := by
  have he : deriv (hu.kinkBase hL hg) = fun y =>
      ((β₀ * u 0 - βL * u L + reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) L -
        2 * reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) y) / (2 * D)) :=
    funext (fun y => (hu.kinkBase_hasDerivAt hL hg y).deriv)
  rw [he]
  have hd := ((hasDerivAt_const z
    (β₀ * u 0 - βL * u L + reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) L)).sub
      ((reflectedFellerRawPrimitive_derivative L hL (reflectedRobinKinkSource L g hg) z).const_mul 2)).div_const
        (2 * D)
  dsimp only [Pi.sub_apply] at hd
  rw [hd.deriv, reflectedRobinKinkSource_extension hL hg hz]
  field_simp [hD.ne']
  ring

theorem ReflectedRobinWeakEquation.kink_conservation (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hg : ContinuousOn g (Icc 0 L)) :
    (∑ i, κ i * u (a i)) + β₀ * u 0 + βL * u L =
      reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) L := by
  have hw := hu.weak_form (fun _ => 1) (IntervalEnergy.const 1 0 L)
  simp only [deriv_const, mul_zero, intervalIntegral.integral_zero, zero_add, mul_one] at hw
  rw [hw]
  apply intervalIntegral.integral_congr_Ioo_of_le hL.le
  intro x hx
  exact (reflectedRobinKinkSource_extension hL hg (Ioo_subset_Icc_self hx)).symm

theorem ReflectedRobinWeakEquation.kinkCoefficient_reaction (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hD : 0 < D) (i : ι) : 2 * D * hu.kinkCoefficient i = κ i * u (a i) := by
  unfold kinkCoefficient
  field_simp [hD.ne']

theorem ReflectedRobinWeakEquation.kinkCoefficient_sum (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hg : ContinuousOn g (Icc 0 L)) :
    (∑ i, hu.kinkCoefficient i) =
      (reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) L - β₀ * u 0 - βL * u L) / (2 * D) := by
  unfold kinkCoefficient
  rw [← Finset.sum_div]
  congr 1
  linarith [hu.kink_conservation hL hg]

end TimeTraps.Probability

end
