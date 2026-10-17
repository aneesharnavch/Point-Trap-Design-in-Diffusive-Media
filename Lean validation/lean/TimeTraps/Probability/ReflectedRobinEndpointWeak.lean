module

public import TimeTraps.Probability.ReflectedRobinWeakFinite
public import TimeTraps.Interval.EndpointPhysicalState
public import TimeTraps.Interval.ReversibleResistanceWeakData

@[expose] public section

/-! The original variable-medium endpoint equation is transported through
the full H1 resistance coordinate. Both physical endpoint strengths and
all interior strengths are unchanged. The source is the actual clock
speed (a*rho) composed with the inverse resistance coordinate. The
architecture can have no interior sites. -/

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval

variable {A : EndpointArchitecture} {K : ℝ}

theorem reflectedRobinEndpoint_form (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K)
    {u v : ℝ → ℝ} (hu : IntervalEnergy u D.source.left D.source.right)
    (hv : IntervalEnergy v D.source.left D.source.right) :
    (∫ x in D.source.left..D.source.right, D.conductance x * deriv u x * deriv v x) +
      (R.leftStrength * u D.source.left * v D.source.left +
        (∑ i, R.interiorStrength i * u (D.site i) * v (D.site i)) +
        R.rightStrength * u D.source.right * v D.source.right) =
    1 * (∫ y in (0 : ℝ)..D.medium.resistanceLength,
      deriv (D.medium.resistanceProfile u) y * deriv (D.medium.resistanceProfile v) y) +
      (∑ i, R.interiorStrength i * D.medium.resistanceProfile u (D.medium.resistance (D.site i)) *
        D.medium.resistanceProfile v (D.medium.resistance (D.site i))) +
      R.leftStrength * D.medium.resistanceProfile u 0 * D.medium.resistanceProfile v 0 +
      R.rightStrength * D.medium.resistanceProfile u D.medium.resistanceLength *
        D.medium.resistanceProfile v D.medium.resistanceLength := by
  erw [one_mul, D.medium.resistance_h1_bilinear hu hv]
  have hs : (∑ i, R.interiorStrength i * D.medium.resistanceProfile u (D.medium.resistance (D.site i)) *
      D.medium.resistanceProfile v (D.medium.resistance (D.site i))) =
      ∑ i, R.interiorStrength i * u (D.site i) * v (D.site i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [D.resistanceProfile_site u i, D.resistanceProfile_site v i]
  rw [hs]
  have hleft : D.medium.source.left = D.source.left := rfl
  have hright : D.medium.source.right = D.source.right := rfl
  simp only [IntervalMedium.resistanceProfile, D.medium.resistanceInverse_zero,
    D.medium.resistanceInverse_length, hleft, hright]
  ring

theorem endpointWeakEquation_resistance
    {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) :
    ReflectedRobinWeakEquation D.medium.resistanceLength 1
      (fun i => D.medium.resistance (D.site i)) R.interiorStrength R.leftStrength R.rightStrength
      D.medium.resistanceSpeed (D.medium.resistanceProfile u) := by
  refine ⟨(D.medium.resistance_h1_profile hu.energy).1, ?_⟩
  intro v hv
  have hvp := (D.medium.resistance_h1_pullback hv).1
  have htv := D.medium.resistance_profile_pullback v
  have he := hu.expanded_weak_form (fun x => v (D.medium.resistance x)) hvp
  rw [reflectedRobinEndpoint_form D R hu.energy hvp] at he
  erw [D.medium.resistance_forcing_integral] at he
  have hd := (htv.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  have hi : (∫ y in (0 : ℝ)..D.medium.resistanceLength,
      deriv (D.medium.resistanceProfile u) y *
        deriv (D.medium.resistanceProfile (fun x => v (D.medium.resistance x))) y) =
      ∫ y in (0 : ℝ)..D.medium.resistanceLength, deriv (D.medium.resistanceProfile u) y * deriv v y := by
    apply intervalIntegral.integral_congr_Ioo_of_le D.medium.resistanceLength_pos.le
    intro y hy
    dsimp only
    rw [hd hy]
  have hs : (∑ i, R.interiorStrength i * D.medium.resistanceProfile u (D.medium.resistance (D.site i)) *
      D.medium.resistanceProfile (fun x => v (D.medium.resistance x)) (D.medium.resistance (D.site i))) =
      ∑ i, R.interiorStrength i * D.medium.resistanceProfile u (D.medium.resistance (D.site i)) *
        v (D.medium.resistance (D.site i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [htv (Ioo_subset_Icc_self (D.medium.resistance_interior (D.site_interior i)))]
  have hf : (∫ y in (0 : ℝ)..D.medium.resistanceLength,
      D.medium.resistanceSpeed y * D.medium.resistanceProfile (fun x => v (D.medium.resistance x)) y) =
      ∫ y in (0 : ℝ)..D.medium.resistanceLength, D.medium.resistanceSpeed y * v y := by
    apply intervalIntegral.integral_congr_Ioo_of_le D.medium.resistanceLength_pos.le
    intro y hy
    dsimp only
    rw [htv (Ioo_subset_Icc_self hy)]
  rw [hi, hs, htv ⟨le_rfl, D.medium.resistanceLength_pos.le⟩,
    htv ⟨D.medium.resistanceLength_pos.le, le_rfl⟩, hf] at he
  exact he

theorem endpointWeakEquation_resistance_iff
    (D : OrderedMedium A.interiorCount) (R : EndpointReactions A K) (u : ℝ → ℝ) :
    EndpointWeakEquation D R u ↔
      ReflectedRobinWeakEquation D.medium.resistanceLength 1
        (fun i => D.medium.resistance (D.site i)) R.interiorStrength R.leftStrength R.rightStrength
        D.medium.resistanceSpeed (D.medium.resistanceProfile u) := by
  refine ⟨endpointWeakEquation_resistance, ?_⟩
  intro hu
  have hue := (D.medium.resistance_h1_iff u).mpr hu.energy
  refine ⟨hue, ?_⟩
  intro v hv
  have he := hu.weak_form (D.medium.resistanceProfile v) (D.medium.resistance_h1_profile hv).1
  rw [← reflectedRobinEndpoint_form D R hue hv, ← D.medium.resistance_forcing_integral] at he
  have hn : (∑ k, R.nodal k * u (D.node k) * v (D.node k)) =
      R.leftStrength * u D.source.left * v D.source.left +
        (∑ i, R.interiorStrength i * u (D.site i) * v (D.site i)) +
        R.rightStrength * u D.source.right * v D.source.right := by
    simp_rw [mul_assoc]
    rw [R.nodal_pairing]
    simp only [D.node_first, D.node_last, OrderedMedium.site]
  rw [hn]
  exact he

end TimeTraps.Probability
