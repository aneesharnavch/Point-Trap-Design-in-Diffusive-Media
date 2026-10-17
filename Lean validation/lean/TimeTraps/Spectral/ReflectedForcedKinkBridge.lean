module

public import TimeTraps.Spectral.ReflectedForcedKinkData
public import TimeTraps.Analysis.ReflectedMeanKinkGreen

@[expose] public section

/-! The absolute-value and constant functions are actual full-H1 tests.
They derive the continuous-source finite-kink representation and both
reflecting slopes directly from the weak equation. No differentiability
of the source or additional regularity of the state is assumed. -/

noncomputable section

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Probability
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {g u : ℝ → ℝ}

theorem WeakForcedEquation.kinkPotential_eq (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) :
    EqOn (hu.kinkPotential hg) u (Icc (0 : ℝ) P.length) := by
  intro y hy
  have hw := hu.weak_form (fun z => |z - y|)
    (intervalEnergy_abs_sub y 0 P.length P.length_pos.le)
  dsimp only [intervalPointForm] at hw
  rw [hu.energy.abs_sub_pairing hy] at hw
  have hk : (∫ z in 0..P.length, g z * |z - y|) =
      (P.length - y) * reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length -
        reflectedNeumannDoublePrimitive P.length P.length_pos (forcedKinkSource P g hg) P.length +
          2 * reflectedNeumannDoublePrimitive P.length P.length_pos (forcedKinkSource P g hg) y := by
    calc
      _ = ∫ z in 0..P.length,
          reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg) z * |z - y| := by
        apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
        intro z hz
        dsimp only
        rw [forcedKinkSource_extension hg (Ioo_subset_Icc_self hz)]
      _ = _ := reflectedEigenstate_abs_integral P.length P.length_pos (forcedKinkSource P g hg) hy
  have hs : (∑ i, hu.kinkCoefficient i * |y - P.site i|) =
      (∑ i, P.strength i * u (P.site i) * |P.site i - y|) / (2 * P.diffusivity) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_sub_comm y (P.site i)]
    unfold WeakForcedEquation.kinkCoefficient
    ring
  change hu.kinkBase hg y + (∑ i, hu.kinkCoefficient i * |y - P.site i|) = u y
  rw [hs]
  unfold WeakForcedEquation.kinkBase
  rw [← hk, ← add_div]
  apply (div_eq_iff (mul_ne_zero (by norm_num) P.diffusivity_pos.ne')).mpr
  nlinarith [hw]

theorem WeakForcedEquation.kinkSlope_endpoints (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) :
    finiteKinkSlope (hu.kinkBase hg) Finset.univ P.site hu.kinkCoefficient 0 = 0 ∧
      finiteKinkSlope (hu.kinkBase hg) Finset.univ P.site hu.kinkCoefficient P.length = 0 := by
  have hs0 (i : Fin n) : Real.sign (0 - P.site i) = -1 :=
    Real.sign_of_neg (sub_neg.mpr (P.site_interior i).1)
  have hsL (i : Fin n) : Real.sign (P.length - P.site i) = 1 :=
    Real.sign_of_pos (sub_pos.mpr (P.site_interior i).2)
  have hR0 : reflectedFellerRawPrimitive P.length P.length_pos (forcedKinkSource P g hg) 0 = 0 := by
    simp only [reflectedFellerRawPrimitive, intervalIntegral.integral_same]
  constructor
  · simp only [finiteKinkSlope, (hu.kinkBase_hasDerivAt hg 0).deriv, hs0,
      mul_neg_one, Finset.sum_neg_distrib, hu.kinkCoefficient_sum hg, hR0]
    ring
  · simp only [finiteKinkSlope, (hu.kinkBase_hasDerivAt hg P.length).deriv, hsL,
      mul_one, hu.kinkCoefficient_sum hg]
    ring

theorem WeakForcedEquation.kinkPotential_neumann (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) :
    HasDerivAt (hu.kinkPotential hg) 0 0 ∧ HasDerivAt (hu.kinkPotential hg) 0 P.length := by
  have hdiff := (hu.kinkBase_contDiff hg).differentiable (by norm_num)
  constructor
  · have he := finiteKinkPotential_hasDerivAt (hdiff.differentiableAt (x := 0))
      Finset.univ P.site hu.kinkCoefficient (fun i _ => ne_of_lt (P.site_interior i).1)
    rw [(hu.kinkSlope_endpoints hg).1] at he
    exact he
  · have he := finiteKinkPotential_hasDerivAt (hdiff.differentiableAt (x := P.length))
      Finset.univ P.site hu.kinkCoefficient (fun i _ => ne_of_gt (P.site_interior i).2)
    rw [(hu.kinkSlope_endpoints hg).2] at he
    exact he

theorem WeakForcedEquation.kinkPotential_reaction (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) (i : Fin n) :
    2 * P.diffusivity * hu.kinkCoefficient i = P.strength i * hu.kinkPotential hg (P.site i) := by
  rw [hu.kinkPotential_eq hg (Ioo_subset_Icc_self (P.site_interior i))]
  exact hu.kinkCoefficient_reaction i

theorem WeakForcedEquation.kinkBase_source (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) {z : ℝ} (hz : z ∈ Icc 0 P.length) :
    P.diffusivity * deriv (deriv (hu.kinkBase hg)) z = -g z := by
  rw [hu.kinkBase_curvature hg hz]
  field_simp [P.diffusivity_pos.ne']

theorem WeakForcedEquation.kink_representation (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) :
    ∃ (F : ℝ → ℝ) (c : Fin n → ℝ), ContDiff ℝ 2 F ∧
      EqOn (finiteKinkPotential F Finset.univ P.site c) u (Icc 0 P.length) ∧
      (∀ z ∈ Icc 0 P.length, P.diffusivity * deriv (deriv F) z = -g z) ∧
      finiteKinkSlope F Finset.univ P.site c 0 = 0 ∧
      finiteKinkSlope F Finset.univ P.site c P.length = 0 ∧
      (∀ i, 2 * P.diffusivity * c i = P.strength i * u (P.site i)) ∧
      (∀ i, 2 * P.diffusivity * c i =
        P.strength i * finiteKinkPotential F Finset.univ P.site c (P.site i)) :=
  ⟨hu.kinkBase hg, hu.kinkCoefficient, hu.kinkBase_contDiff hg, hu.kinkPotential_eq hg,
    fun _ hz => hu.kinkBase_source hg hz, (hu.kinkSlope_endpoints hg).1,
    (hu.kinkSlope_endpoints hg).2, hu.kinkCoefficient_reaction, hu.kinkPotential_reaction hg⟩

theorem SpectralProblem.forced_kink_representation (P : SpectralProblem n)
    {g u : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 P.length)) (hu : IntervalEnergy u 0 P.length)
    (hw : ∀ v : ℝ → ℝ, IntervalEnergy v 0 P.length →
      intervalPointForm P.diffusivity P.strength P.site 0 P.length u v =
        ∫ x in (0 : ℝ)..P.length, g x * v x) :
    ∃ (F : ℝ → ℝ) (c : Fin n → ℝ), ContDiff ℝ 2 F ∧
      EqOn (finiteKinkPotential F Finset.univ P.site c) u (Icc 0 P.length) ∧
      (∀ z ∈ Icc 0 P.length, P.diffusivity * deriv (deriv F) z = -g z) ∧
      finiteKinkSlope F Finset.univ P.site c 0 = 0 ∧
      finiteKinkSlope F Finset.univ P.site c P.length = 0 ∧
      (∀ i, 2 * P.diffusivity * c i = P.strength i * u (P.site i)) ∧
      (∀ i, 2 * P.diffusivity * c i =
        P.strength i * finiteKinkPotential F Finset.univ P.site c (P.site i)) :=
  (show WeakForcedEquation P g u from ⟨hu, hw⟩).kink_representation hg

end TimeTraps.Spectral

end
