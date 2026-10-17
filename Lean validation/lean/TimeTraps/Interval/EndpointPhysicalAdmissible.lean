module

public import TimeTraps.Interval.EndpointPhysicalState

@[expose] public section

/-!
The independent physical design class is nonempty for every mixed
architecture, positive budget and positive continuous medium. Equal active
strengths and equally spaced interior sites give one admissible design;
no optimality or balanced-cell property is asserted for this example.
-/

namespace TimeTraps.Interval

open scoped BigOperators

noncomputable def EndpointReactions.uniform (A : EndpointArchitecture) {K : ℝ}
    (hK : 0 < K) : EndpointReactions A K where
  interiorStrength _ := K / A.count
  leftStrength := if A.leftReactive = true then K / A.count else 0
  rightStrength := if A.rightReactive = true then K / A.count else 0
  interior_pos _ := div_pos hK (by exact_mod_cast A.count_pos)
  left_condition := by
    split_ifs
    · exact div_pos hK (by exact_mod_cast A.count_pos)
    · rfl
  right_condition := by
    split_ifs
    · exact div_pos hK (by exact_mod_cast A.count_pos)
    · rfl
  total_strength := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs : (if A.leftReactive = true then K / A.count else 0) +
        (A.interiorCount : ℝ) * (K / A.count) +
        (if A.rightReactive = true then K / A.count else 0) =
        (A.count : ℝ) * (K / A.count) := by
      cases hl : A.leftReactive <;> cases hr : A.rightReactive <;>
        simp [EndpointArchitecture.count, hl, hr, Nat.cast_add] <;> ring
    rw [hs]
    have hn : (A.count : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt A.count_pos)
    field_simp

noncomputable def IntervalMedium.endpointGeometry (B : IntervalMedium)
    (A : EndpointArchitecture) : OrderedMedium A.interiorCount where
  source := B.source
  conductance := B.conductance
  conductance_continuous := B.conductance_continuous
  conductance_pos := B.conductance_pos
  node i := B.source.left + (i.val : ℝ) * (B.source.right - B.source.left) /
    ((A.interiorCount : ℝ) + 1)
  node_strictMono := by
    intro i j hij
    have hi : (i.val : ℝ) < j.val := by exact_mod_cast hij
    have hd := div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_right hi (sub_pos.mpr B.source.increasing))
      (show 0 < (A.interiorCount : ℝ) + 1 by positivity)
    dsimp only
    linarith
  node_first := by simp
  node_last := by
    simp only [Fin.val_last, Nat.cast_add, Nat.cast_one]
    have hn : (A.interiorCount : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem IntervalMedium.endpointGeometry_medium (B : IntervalMedium) (A : EndpointArchitecture) :
    (B.endpointGeometry A).medium = B := rfl

noncomputable def EndpointPhysicalDesign.admissible (A : EndpointArchitecture)
    (B : IntervalMedium) {K : ℝ} (hK : 0 < K) : EndpointPhysicalDesign A B K :=
  EndpointPhysicalDesign.ofGeometry (B.endpointGeometry A) (EndpointReactions.uniform A hK)

theorem endpoint_physical_design_nonempty (A : EndpointArchitecture) (B : IntervalMedium)
    {K : ℝ} (hK : 0 < K) : Nonempty (EndpointPhysicalDesign A B K) :=
  ⟨EndpointPhysicalDesign.admissible A B hK⟩

end TimeTraps.Interval
