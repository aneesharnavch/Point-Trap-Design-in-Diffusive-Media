module

public import TimeTraps.Interval.EndpointSourceReactions
public import TimeTraps.Interval.SourceWeakTransform

@[expose] public section

/-! Exact source-coordinate equivalence of the complete endpoint weak
problem. Both directions quantify over the full H1 test space. Reactions
and budget divide by source mass, the effective conductance is Ω⁻¹, and
the actual objective and absorption partition are preserved. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {A : EndpointArchitecture} {K : ℝ}

theorem endpoint_source_weak_transform_iff (D : OrderedMedium A.interiorCount)
    (R : EndpointReactions A K) (u : ℝ → ℝ) :
    EndpointWeakEquation D R u ↔
      EndpointWeakEquation (sourceWeakUnitGeometry D) (R.normalize D.source.mass D.source.mass_pos)
        (D.source.transformed u) := by
  constructor
  · intro hu
    refine ⟨(source_h1_inverse D.source hu.energy).1, ?_⟩
    intro v hv
    have hvp := (source_h1_coordinate D.source hv).1
    have he := hu.weak_form (fun x => v (D.source.coordinate x)) hvp
    have hb := source_h1_bilinear D.medium hu.energy hvp
    have htv := source_h1_transformed_pullback D.source v
    have htd := (htv.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
    have hbi : (∫ z in (0 : ℝ)..1, sourceMeanConductance D.medium z *
        deriv (D.source.transformed u) z *
          deriv (D.source.transformed (fun x => v (D.source.coordinate x))) z) =
        ∫ z in (0 : ℝ)..1, sourceMeanConductance D.medium z * deriv (D.source.transformed u) z * deriv v z := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro z hz
      dsimp only
      rw [htd hz]
    change (∫ x in D.source.left..D.source.right, D.conductance x * deriv u x *
      deriv (fun y => v (D.source.coordinate y)) x) = D.source.mass *
        ∫ z in (0 : ℝ)..1, sourceMeanConductance D.medium z * deriv (D.source.transformed u) z *
          deriv (D.source.transformed (fun x => v (D.source.coordinate x))) z at hb
    rw [hbi] at hb
    have hρ := D.source.source_integral (hvp.continuousOn.mono Icc_subset_uIcc)
    have hti : (∫ z in (0 : ℝ)..1, D.source.transformed (fun x => v (D.source.coordinate x)) z) =
        ∫ z in (0 : ℝ)..1, v z := by
      apply intervalIntegral.integral_congr
      intro z hz
      exact htv (by simpa only [uIcc_of_le zero_le_one] using hz)
    rw [hti] at hρ
    have hr : D.source.mass * (∑ k, (R.normalize D.source.mass D.source.mass_pos).nodal k *
        D.source.transformed u ((sourceWeakUnitGeometry D).node k) * v ((sourceWeakUnitGeometry D).node k)) =
        ∑ k, R.nodal k * u (D.node k) * v (D.source.coordinate (D.node k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [R.normalize_nodal]
      change D.source.mass * (R.nodal k / D.source.mass *
        D.source.transformed u (D.source.coordinate (D.node k)) * v (D.source.coordinate (D.node k))) = _
      rw [D.source.transformed_coordinate u (D.node_mem k)]
      field_simp [ne_of_gt D.source.mass_pos]
    change (∫ z in (0 : ℝ)..1, sourceMeanConductance D.medium z * deriv (D.source.transformed u) z * deriv v z) +
      (∑ k, (R.normalize D.source.mass D.source.mass_pos).nodal k *
        D.source.transformed u ((sourceWeakUnitGeometry D).node k) * v ((sourceWeakUnitGeometry D).node k)) =
          ∫ z in (0 : ℝ)..1, 1 * v z
    simp only [one_mul]
    apply mul_left_cancel₀ (ne_of_gt D.source.mass_pos)
    rw [mul_add, ← hb, hr, ← hρ]
    exact he
  · intro hu
    have hup := (source_h1_iff D.source u).mpr hu.energy
    refine ⟨hup, ?_⟩
    intro v hv
    have hvt := (source_h1_inverse D.source hv).1
    have he := hu.weak_form (D.source.transformed v) hvt
    change (∫ z in (0 : ℝ)..1, sourceMeanConductance D.medium z *
      deriv (D.source.transformed u) z * deriv (D.source.transformed v) z) +
      (∑ k, (R.normalize D.source.mass D.source.mass_pos).nodal k *
        D.source.transformed u ((sourceWeakUnitGeometry D).node k) *
          D.source.transformed v ((sourceWeakUnitGeometry D).node k)) =
        ∫ z in (0 : ℝ)..1, 1 * D.source.transformed v z at he
    simp only [one_mul] at he
    have hb := source_h1_bilinear D.medium hup hv
    change (∫ x in D.source.left..D.source.right, D.conductance x * deriv u x * deriv v x) =
      D.source.mass * ∫ z in (0 : ℝ)..1, sourceMeanConductance D.medium z *
        deriv (D.source.transformed u) z * deriv (D.source.transformed v) z at hb
    have hρ := D.source.source_integral (hv.continuousOn.mono Icc_subset_uIcc)
    have hr : D.source.mass * (∑ k, (R.normalize D.source.mass D.source.mass_pos).nodal k *
        D.source.transformed u ((sourceWeakUnitGeometry D).node k) *
          D.source.transformed v ((sourceWeakUnitGeometry D).node k)) =
        ∑ k, R.nodal k * u (D.node k) * v (D.node k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [R.normalize_nodal]
      change D.source.mass * (R.nodal k / D.source.mass *
        D.source.transformed u (D.source.coordinate (D.node k)) *
          D.source.transformed v (D.source.coordinate (D.node k))) = _
      rw [D.source.transformed_coordinate u (D.node_mem k), D.source.transformed_coordinate v (D.node_mem k)]
      field_simp [ne_of_gt D.source.mass_pos]
    change (∫ x in D.source.left..D.source.right, D.conductance x * deriv u x * deriv v x) +
      (∑ k, R.nodal k * u (D.node k) * v (D.node k)) =
        ∫ x in D.source.left..D.source.right, D.source.density x * v x
    rw [hb, ← hr, ← mul_add, he, ← hρ]

theorem EndpointWeakEquation.normalized_weak_form {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {u : ℝ → ℝ} (hu : EndpointWeakEquation D R u)
    (v : ℝ → ℝ) (hv : IntervalEnergy v 0 1) :
    (∫ z in (0 : ℝ)..1, (D.source.weight D.conductance z)⁻¹ *
      deriv (D.source.transformed u) z * deriv v z) +
      (R.leftStrength / D.source.mass) * D.source.transformed u 0 * v 0 +
      (∑ i, (R.interiorStrength i / D.source.mass) * D.source.transformed u (D.sourceSite i) * v (D.sourceSite i)) +
      (R.rightStrength / D.source.mass) * D.source.transformed u 1 * v 1 = ∫ z in (0 : ℝ)..1, v z := by
  have he := ((endpoint_source_weak_transform_iff D R u).mp hu).expanded_weak_form v hv
  change (∫ z in (0 : ℝ)..1, (1 / D.source.weight D.conductance z) *
      deriv (D.source.transformed u) z * deriv v z) +
      ((R.leftStrength / D.source.mass) * D.source.transformed u 0 * v 0 +
      (∑ i, (R.interiorStrength i / D.source.mass) * D.source.transformed u (D.sourceSite i) * v (D.sourceSite i)) +
      (R.rightStrength / D.source.mass) * D.source.transformed u 1 * v 1) = ∫ z in (0 : ℝ)..1, 1 * v z at he
  simpa only [one_div, one_mul, add_assoc] using he

theorem EndpointWeakEquation.source_norm_eq {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {u : ℝ → ℝ} (hu : EndpointWeakEquation D R u) :
    (sourceWeakUnitGeometry D).essentialNorm (D.source.transformed u) = D.essentialNorm u := by
  have ht := ((endpoint_source_weak_transform_iff D R u).mp hu).essentialNorm_isGreatest
  change IsGreatest (D.source.transformed u '' Icc (0 : ℝ) 1)
    ((sourceWeakUnitGeometry D).essentialNorm (D.source.transformed u)) at ht
  apply le_antisymm
  · obtain ⟨z, _, he⟩ := ht.1
    rw [← he]
    exact hu.essentialNorm_isGreatest.2 ⟨D.source.inverse z, D.source.inverse_mem z, rfl⟩
  · obtain ⟨x, hx, he⟩ := hu.essentialNorm_isGreatest.1
    rw [← he]
    exact ht.2 ⟨D.source.coordinate x, D.source.coordinate_mem hx, D.source.transformed_coordinate u hx⟩

theorem EndpointReactions.source_activeShare (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) (u : ℝ → ℝ) (i : Fin A.count) :
    (R.normalize D.source.mass D.source.mass_pos).activeShare (sourceWeakUnitGeometry D)
      (D.source.transformed u) i = R.activeShare D u i := by
  unfold activeShare
  rw [R.normalize_activeStrength]
  have hm : (sourceWeakUnitGeometry D).source.mass = 1 := homogeneous_mass zero_lt_one zero_lt_one
  rw [hm, div_one]
  change (R.activeStrength i / D.source.mass) *
    D.source.transformed u (D.source.coordinate (D.node (A.activeNode i))) = _
  rw [D.source.transformed_coordinate u (D.node_mem _)]
  dsimp only [EndpointArchitecture.physicalSite]
  ring

theorem EndpointWeakEquation.source_partition_eq {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {u : ℝ → ℝ} (hu : EndpointWeakEquation D R u) :
    ((endpoint_source_weak_transform_iff D R u).mp hu).partition = hu.partition := by
  have hs : (R.normalize D.source.mass D.source.mass_pos).activeShare (sourceWeakUnitGeometry D)
      (D.source.transformed u) = R.activeShare D u := funext (R.source_activeShare D u)
  have hp : ((endpoint_source_weak_transform_iff D R u).mp hu).partition.point = hu.partition.point := by
    funext e
    rw [EndpointWeakEquation.partition_point, EndpointWeakEquation.partition_point, hs]
  generalize ((endpoint_source_weak_transform_iff D R u).mp hu).partition = P at hp ⊢
  generalize hu.partition = Q at hp ⊢
  cases P
  cases Q
  congr

end TimeTraps.Interval
