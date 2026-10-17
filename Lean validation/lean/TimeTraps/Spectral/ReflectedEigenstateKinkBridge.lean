module

public import TimeTraps.Spectral.ReflectedEigenstateKinkData
public import TimeTraps.Analysis.ReflectedMeanKinkGreen

@[expose] public section

/-! Exact finite-kink representation of every original weak eigenstate.
The full H¹ Green test proves equality, and the constant test proves the
two reflecting slopes. The signed kink reactions are derived at all sites. -/

noncomputable section

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Probability
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ} {u : ℝ → ℝ}

theorem WeakEigenEquation.kinkPotential_eq (hu : WeakEigenEquation P ev u) :
    EqOn hu.kinkPotential u (Icc (0 : ℝ) P.length) := by
  intro y hy
  have hw := hu.weak_form (fun z => |z - y|)
    (intervalEnergy_abs_sub y 0 P.length P.length_pos.le)
  rw [hu.energy.abs_sub_pairing hy] at hw
  have hk : (∫ z in 0..P.length, u z * |z - y|) =
      (P.length - y) * reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile P.length -
        reflectedNeumannDoublePrimitive P.length P.length_pos hu.kinkProfile P.length +
          2 * reflectedNeumannDoublePrimitive P.length P.length_pos hu.kinkProfile y := by
    calc
      _ = ∫ z in 0..P.length, reflectedFellerExtension P.length P.length_pos hu.kinkProfile z * |z - y| := by
        apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
        intro z hz
        dsimp only
        rw [hu.kinkProfile_extension (Ioo_subset_Icc_self hz)]
      _ = _ := reflectedEigenstate_abs_integral P.length P.length_pos hu.kinkProfile hy
  have hs : (∑ i, hu.kinkCoefficient i * |y - P.site i|) =
      (∑ i, P.strength i * u (P.site i) * |P.site i - y|) / (2 * P.diffusivity) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_sub_comm y (P.site i)]
    unfold WeakEigenEquation.kinkCoefficient
    ring
  change hu.kinkBase y + (∑ i, hu.kinkCoefficient i * |y - P.site i|) = u y
  rw [hs]
  unfold WeakEigenEquation.kinkBase
  rw [← hk, ← add_div]
  apply (div_eq_iff (mul_ne_zero (by norm_num) P.diffusivity_pos.ne')).mpr
  nlinarith [hw]

theorem WeakEigenEquation.kinkSlope_endpoints (hu : WeakEigenEquation P ev u) :
    finiteKinkSlope hu.kinkBase Finset.univ P.site hu.kinkCoefficient 0 = 0 ∧
      finiteKinkSlope hu.kinkBase Finset.univ P.site hu.kinkCoefficient P.length = 0 := by
  have hs0 (i : Fin n) : Real.sign (0 - P.site i) = -1 :=
    Real.sign_of_neg (sub_neg.mpr (P.site_interior i).1)
  have hsL (i : Fin n) : Real.sign (P.length - P.site i) = 1 :=
    Real.sign_of_pos (sub_pos.mpr (P.site_interior i).2)
  have hR0 : reflectedFellerRawPrimitive P.length P.length_pos hu.kinkProfile 0 = 0 := by
    simp only [reflectedFellerRawPrimitive, intervalIntegral.integral_same]
  constructor
  · simp only [finiteKinkSlope, (hu.kinkBase_hasDerivAt 0).deriv, hs0,
      mul_neg_one, Finset.sum_neg_distrib, hu.kinkCoefficient_sum, hR0]
    ring
  · simp only [finiteKinkSlope, (hu.kinkBase_hasDerivAt P.length).deriv, hsL,
      mul_one, hu.kinkCoefficient_sum]
    ring

theorem WeakEigenEquation.kinkPotential_neumann (hu : WeakEigenEquation P ev u) :
    HasDerivAt hu.kinkPotential 0 0 ∧ HasDerivAt hu.kinkPotential 0 P.length := by
  have hdiff := hu.kinkBase_contDiff.differentiable (by norm_num)
  constructor
  · have he := finiteKinkPotential_hasDerivAt (hdiff.differentiableAt (x := 0))
      Finset.univ P.site hu.kinkCoefficient (fun i _ => ne_of_lt (P.site_interior i).1)
    rw [hu.kinkSlope_endpoints.1] at he
    exact he
  · have he := finiteKinkPotential_hasDerivAt (hdiff.differentiableAt (x := P.length))
      Finset.univ P.site hu.kinkCoefficient (fun i _ => ne_of_gt (P.site_interior i).2)
    rw [hu.kinkSlope_endpoints.2] at he
    exact he

theorem WeakEigenEquation.kinkPotential_reaction (hu : WeakEigenEquation P ev u) (i : Fin n) :
    2 * P.diffusivity * hu.kinkCoefficient i = P.strength i * hu.kinkPotential (P.site i) := by
  rw [hu.kinkPotential_eq (Ioo_subset_Icc_self (P.site_interior i))]
  exact hu.kinkCoefficient_reaction i

theorem WeakEigenEquation.kinkBase_curvature_potential (hu : WeakEigenEquation P ev u)
    {z : ℝ} (hz : z ∈ Icc 0 P.length) :
    deriv (deriv hu.kinkBase) z = -ev * hu.kinkPotential z / P.diffusivity := by
  rw [hu.kinkPotential_eq hz]
  exact hu.kinkBase_curvature hz

end TimeTraps.Spectral

end
