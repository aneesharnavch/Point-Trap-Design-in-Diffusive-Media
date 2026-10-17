module

public import TimeTraps.Probability.ReflectedRobinWeakData

@[expose] public section

/-! Constant and absolute-value H1 tests derive the full global finite-
kink representation and both physical Robin slope conditions. No state
smoothness beyond H1, source differentiability, or extra endpoint test
restriction is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {L D : ℝ} {a κ : ι → ℝ} {β₀ βL : ℝ} {g u : ℝ → ℝ}

theorem ReflectedRobinWeakEquation.kinkPotential_eq
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (hg : ContinuousOn g (Icc 0 L)) :
    EqOn (hu.kinkPotential hL hg) u (Icc (0 : ℝ) L) := by
  intro y hy
  have hw := hu.weak_form (fun z => |z - y|) (intervalEnergy_abs_sub y 0 L hL.le)
  rw [hu.energy.abs_sub_pairing hy] at hw
  have hy0 : |0 - y| = y := by rw [zero_sub, abs_neg, abs_of_nonneg hy.1]
  have hyL : |L - y| = L - y := abs_of_nonneg (sub_nonneg.mpr hy.2)
  rw [hy0, hyL] at hw
  have hk : (∫ z in 0..L, g z * |z - y|) =
      (L - y) * reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) L -
        reflectedNeumannDoublePrimitive L hL (reflectedRobinKinkSource L g hg) L +
          2 * reflectedNeumannDoublePrimitive L hL (reflectedRobinKinkSource L g hg) y := by
    calc
      _ = ∫ z in 0..L, reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg) z * |z - y| := by
        apply intervalIntegral.integral_congr_Ioo_of_le hL.le
        intro z hz
        dsimp only
        rw [reflectedRobinKinkSource_extension hL hg (Ioo_subset_Icc_self hz)]
      _ = _ := TimeTraps.Spectral.reflectedEigenstate_abs_integral L hL (reflectedRobinKinkSource L g hg) hy
  have hs : (∑ i, hu.kinkCoefficient i * |y - a i|) =
      (∑ i, κ i * u (a i) * |a i - y|) / (2 * D) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_sub_comm y (a i)]
    unfold ReflectedRobinWeakEquation.kinkCoefficient
    ring
  change hu.kinkBase hL hg y + (∑ i, hu.kinkCoefficient i * |y - a i|) = u y
  rw [hs]
  unfold ReflectedRobinWeakEquation.kinkBase
  rw [← hk, ← add_div]
  apply (div_eq_iff (mul_ne_zero (by norm_num) hD.ne')).mpr
  nlinarith [hw]

theorem ReflectedRobinWeakEquation.kinkSlope_endpoints
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hg : ContinuousOn g (Icc 0 L)) :
    D * finiteKinkSlope (hu.kinkBase hL hg) Finset.univ a hu.kinkCoefficient 0 = β₀ * u 0 ∧
      D * finiteKinkSlope (hu.kinkBase hL hg) Finset.univ a hu.kinkCoefficient L = -βL * u L := by
  have hs0 (i : ι) : Real.sign (0 - a i) = -1 := Real.sign_of_neg (sub_neg.mpr (ha i).1)
  have hsL (i : ι) : Real.sign (L - a i) = 1 := Real.sign_of_pos (sub_pos.mpr (ha i).2)
  have hR0 : reflectedFellerRawPrimitive L hL (reflectedRobinKinkSource L g hg) 0 = 0 := by
    simp only [reflectedFellerRawPrimitive, intervalIntegral.integral_same]
  constructor
  · simp only [finiteKinkSlope, (hu.kinkBase_hasDerivAt hL hg 0).deriv, hs0,
      mul_neg_one, Finset.sum_neg_distrib, hu.kinkCoefficient_sum hL hg, hR0]
    field_simp [hD.ne']
    ring
  · simp only [finiteKinkSlope, (hu.kinkBase_hasDerivAt hL hg L).deriv, hsL,
      mul_one, hu.kinkCoefficient_sum hL hg]
    field_simp [hD.ne']
    ring

theorem ReflectedRobinWeakEquation.kinkPotential_reaction
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L)
    (hg : ContinuousOn g (Icc 0 L)) (i : ι) :
    2 * D * hu.kinkCoefficient i = κ i * hu.kinkPotential hL hg (a i) := by
  rw [hu.kinkPotential_eq hL hD hg (Ioo_subset_Icc_self (ha i))]
  exact hu.kinkCoefficient_reaction hD i

theorem ReflectedRobinWeakEquation.kinkBase_source
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (hg : ContinuousOn g (Icc 0 L)) {z : ℝ} (hz : z ∈ Icc 0 L) :
    D * deriv (deriv (hu.kinkBase hL hg)) z = -g z := by
  rw [hu.kinkBase_curvature hL hD hg hz]
  field_simp [hD.ne']

theorem ReflectedRobinWeakEquation.kinkPotential_robin
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hg : ContinuousOn g (Icc 0 L)) :
    D * finiteKinkSlope (hu.kinkBase hL hg) Finset.univ a hu.kinkCoefficient 0 =
        β₀ * hu.kinkPotential hL hg 0 ∧
      D * finiteKinkSlope (hu.kinkBase hL hg) Finset.univ a hu.kinkCoefficient L =
        -βL * hu.kinkPotential hL hg L := by
  rw [hu.kinkPotential_eq hL hD hg ⟨le_rfl, hL.le⟩,
    hu.kinkPotential_eq hL hD hg ⟨hL.le, le_rfl⟩]
  exact hu.kinkSlope_endpoints hL hD ha hg

theorem ReflectedRobinWeakEquation.kink_representation
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hg : ContinuousOn g (Icc 0 L)) :
    ∃ (F : ℝ → ℝ) (c : ι → ℝ), ContDiff ℝ 2 F ∧
      EqOn (finiteKinkPotential F Finset.univ a c) u (Icc 0 L) ∧
      (∀ z ∈ Icc 0 L, D * deriv (deriv F) z = -g z) ∧
      D * finiteKinkSlope F Finset.univ a c 0 = β₀ * finiteKinkPotential F Finset.univ a c 0 ∧
      D * finiteKinkSlope F Finset.univ a c L = -βL * finiteKinkPotential F Finset.univ a c L ∧
      (∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i)) :=
  ⟨hu.kinkBase hL hg, hu.kinkCoefficient, hu.kinkBase_contDiff hL hg, hu.kinkPotential_eq hL hD hg,
    fun _ hz => hu.kinkBase_source hL hD hg hz, (hu.kinkPotential_robin hL hD ha hg).1,
    (hu.kinkPotential_robin hL hD ha hg).2, hu.kinkPotential_reaction hL hD ha hg⟩

end TimeTraps.Probability

end
