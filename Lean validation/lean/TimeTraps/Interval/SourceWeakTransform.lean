module

public import TimeTraps.Interval.SourceH1Bilinear

@[expose] public section

/-! Equivalence of the complete physical and normalized-source weak
equations, with their full H1 test spaces. The transformed strengths are
κ/S and the effective conductance is a(X)ρ(X)/S². This deterministic theorem
does not assert a stochastic or Revuz-measure identification. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

noncomputable def sourceWeakUnitGeometry (D : OrderedMedium n) : OrderedMedium n where
  source := (homogeneous 1 1 zero_lt_one zero_lt_one).source
  conductance := sourceMeanConductance D.medium
  conductance_continuous := sourceMeanConductance_continuous D.medium
  conductance_pos := sourceMeanConductance_pos D.medium
  node := fun v => D.source.coordinate (D.node v)
  node_strictMono := fun i j hij => D.source.coordinate_strictMono
    (D.node_mem i) (D.node_mem j) (D.node_strictMono hij)
  node_first := by rw [D.node_first, D.source.coordinate_left]; rfl
  node_last := by rw [D.node_last, D.source.coordinate_right]; rfl

theorem sourceWeakUnitGeometry_site (D : OrderedMedium n) (i : Fin n) :
    (sourceWeakUnitGeometry D).site i = D.source.coordinate (D.site i) := rfl

theorem source_h1_transformed_pullback (P : SourceInterval) (v : ℝ → ℝ) :
    EqOn (P.transformed (fun x => v (P.coordinate x))) v (Icc (0 : ℝ) 1) := by
  intro z hz
  change v (P.coordinate (P.inverse z)) = v z
  rw [P.coordinate_inverse hz]

theorem source_weak_transform_iff (D : OrderedMedium n) (κ : Fin n → ℝ) (u : ℝ → ℝ) :
    WeakIntervalEquation D κ u ↔
      WeakIntervalEquation (sourceWeakUnitGeometry D) (fun i => κ i / D.source.mass) (D.source.transformed u) := by
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
    have hr : D.source.mass * (∑ i, (κ i / D.source.mass) *
        D.source.transformed u ((sourceWeakUnitGeometry D).site i) * v ((sourceWeakUnitGeometry D).site i)) =
        ∑ i, κ i * u (D.site i) * v (D.source.coordinate (D.site i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [sourceWeakUnitGeometry_site, D.source.transformed_coordinate u
        (Ioo_subset_Icc_self (D.site_interior i))]
      field_simp [ne_of_gt D.source.mass_pos]
    change (∫ z in (0 : ℝ)..1, sourceMeanConductance D.medium z * deriv (D.source.transformed u) z * deriv v z) +
      (∑ i, (κ i / D.source.mass) * D.source.transformed u ((sourceWeakUnitGeometry D).site i) *
        v ((sourceWeakUnitGeometry D).site i)) = ∫ z in (0 : ℝ)..1, 1 * v z
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
      (∑ i, (κ i / D.source.mass) * D.source.transformed u ((sourceWeakUnitGeometry D).site i) *
        D.source.transformed v ((sourceWeakUnitGeometry D).site i)) =
      ∫ z in (0 : ℝ)..1, 1 * D.source.transformed v z at he
    simp only [one_mul] at he
    have hb := source_h1_bilinear D.medium hup hv
    change (∫ x in D.source.left..D.source.right, D.conductance x * deriv u x * deriv v x) =
      D.source.mass * ∫ z in (0 : ℝ)..1, sourceMeanConductance D.medium z *
        deriv (D.source.transformed u) z * deriv (D.source.transformed v) z at hb
    have hρ := D.source.source_integral (hv.continuousOn.mono Icc_subset_uIcc)
    have hr : D.source.mass * (∑ i, (κ i / D.source.mass) *
        D.source.transformed u ((sourceWeakUnitGeometry D).site i) *
          D.source.transformed v ((sourceWeakUnitGeometry D).site i)) =
        ∑ i, κ i * u (D.site i) * v (D.site i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [sourceWeakUnitGeometry_site, D.source.transformed_coordinate u
        (Ioo_subset_Icc_self (D.site_interior i)), D.source.transformed_coordinate v
          (Ioo_subset_Icc_self (D.site_interior i))]
      field_simp [ne_of_gt D.source.mass_pos]
    change (∫ x in D.source.left..D.source.right, D.conductance x * deriv u x * deriv v x) +
      (∑ i, κ i * u (D.site i) * v (D.site i)) =
      ∫ x in D.source.left..D.source.right, D.source.density x * v x
    rw [hb, ← hr, ← mul_add, he, ← hρ]

end TimeTraps.Interval
