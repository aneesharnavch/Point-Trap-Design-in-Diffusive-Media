module

public import TimeTraps.Spectral.ArrayExner
public import Mathlib.Data.Fin.Rev

@[expose] public section

/-! Explicit rotations and reflections of the regular optimizer. Sorted
representatives have a unique offset in [0,L/n). Reflection permutes their
indices, so allowing reflection adds no further regular equality class. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

noncomputable def regularSites (n : ℕ) (L a : ℝ) (i : Fin n) : ℝ :=
  a + i.val * L / n

theorem regularSites_strictMono (hn : 0 < n) {L a : ℝ} (hL : 0 < L) :
    StrictMono (regularSites n L a) := by
  intro i j hij
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hijR : (i.val : ℝ) < j.val := by exact_mod_cast hij
  exact add_lt_add_right (div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_right hijR hL) hnR) a

theorem PlacementProblem.regularSites_admissible (C : PlacementProblem n)
    {a : ℝ} (ha : a ∈ Ico 0 (C.length / n)) :
    C.AdmissibleArray (regularSites n C.length a) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast C.count_pos
  refine ⟨regularSites_strictMono C.count_pos C.length_pos, fun i => ⟨?_, ?_⟩⟩
  · exact add_nonneg ha.1 (div_nonneg (mul_nonneg (Nat.cast_nonneg _) C.length_pos.le) hnR.le)
  · have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    calc
      regularSites n C.length a i < C.length / n + i.val * C.length / n :=
        add_lt_add_left ha.2 _
      _ = (i.val + 1) * C.length / n := by ring
      _ ≤ C.length := (div_le_iff₀ hnR).mpr (by nlinarith [C.length_pos])

theorem PlacementProblem.regular_offset_range (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.AdmissibleArray x) {a : ℝ}
    (hs : ∀ i, x i = regularSites n C.length a i) : a ∈ Ico 0 (C.length / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast C.count_pos
  let first : Fin n := ⟨0, C.count_pos⟩
  let last : Fin n := ⟨n - 1, by have := C.count_pos; omega⟩
  have hf : x first = a := by simpa [regularSites, first] using hs first
  have hi : (last.val : ℝ) + 1 = n := by
    have hiN : last.val + 1 = n := by dsimp [last]; have := C.count_pos; omega
    exact_mod_cast hiN
  have hsum : last.val * C.length / n + C.length / n = C.length := by
    calc
      last.val * C.length / n + C.length / n = (last.val + 1) * C.length / n := by ring
      _ = C.length := by rw [hi]; field_simp
  have hl := (hx.2 last).2
  rw [hs last] at hl
  dsimp only [regularSites] at hl
  exact ⟨by rw [← hf]; exact (hx.2 first).1, by linarith⟩

theorem PlacementProblem.regular_array_offset (C : PlacementProblem n)
    {a : ℝ} (ha : a ∈ Ico 0 (C.length / n)) :
    (C.array (regularSites n C.length a) (C.regularSites_admissible ha)).offset = a := by
  simp [PeriodicArray.offset, PeriodicArray.first, PlacementProblem.array, regularSites]

theorem regularSites_reflection (L a : ℝ) (i : Fin n) :
    2 * a + ((n : ℝ) - 1) * L / n - regularSites n L a i =
      regularSites n L a i.rev := by
  have hiN : i.val + i.rev.val + 1 = n := by rw [Fin.val_rev]; omega
  have hiR : (i.val : ℝ) + i.rev.val + 1 = n := by exact_mod_cast hiN
  dsimp only [regularSites]
  rw [← hiR]
  ring

theorem regularSites_reflection_range (L a : ℝ) :
    (fun t : ℝ => 2 * a + ((n : ℝ) - 1) * L / n - t) ''
      range (regularSites n L a) = range (regularSites n L a) := by
  ext y
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i.rev, (regularSites_reflection L a i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨regularSites n L a i.rev, ⟨i.rev, rfl⟩, ?_⟩
    simpa only [Fin.rev_rev] using regularSites_reflection L a i.rev

theorem BudgetProblem.array_value_eq_iff_rotation (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleArray x) :
    ((B.placement κ hκ).array x hx).principalValue = B.diffusivity * B.uniform.root ^ 2 ↔
      κ = B.uniformStrength ∧ ∃ a ∈ Ico 0 (B.length / n),
        x = regularSites n B.length a := by
  rw [B.array_value_eq_iff κ hκ x hx]
  constructor
  · rintro ⟨hκeq, hs⟩
    exact ⟨hκeq, _, (B.placement κ hκ).regular_offset_range x hx hs, funext hs⟩
  · rintro ⟨hκeq, a, ha, rfl⟩
    refine ⟨hκeq, fun i => ?_⟩
    have ho := (B.placement κ hκ).regular_array_offset ha
    change a + i.val * B.length / n = _
    rw [show ((B.placement κ hκ).array (regularSites n B.length a) hx).offset = a from ho]

theorem BudgetProblem.rotated_regular_array_value (B : BudgetProblem n)
    {a : ℝ} (ha : a ∈ Ico 0 (B.length / n)) :
    (B.uniform.array (regularSites n B.length a) (B.uniform.regularSites_admissible ha)).principalValue =
      B.diffusivity * B.uniform.root ^ 2 := by
  apply (B.array_value_eq_iff_rotation _ B.uniformStrength_admissible _ _).mpr
  exact ⟨rfl, a, ha, rfl⟩

theorem ExnerProblem.array_value_eq_iff_rotation (E : ExnerProblem n)
    (x : Fin n → ℝ) (hx : E.prescribed.AdmissibleArray x) :
    (E.prescribed.array x hx).principalValue = E.wavenumber ^ 2 ↔
      ∃ a ∈ Ico 0 ((2 * Real.pi) / n), x = regularSites n (2 * Real.pi) a := by
  rw [E.array_value_eq_iff_regular x hx]
  constructor
  · intro hs
    exact ⟨_, E.prescribed.regular_offset_range x hx hs, funext hs⟩
  · rintro ⟨a, ha, rfl⟩
    intro i
    have ho := E.prescribed.regular_array_offset ha
    change a + i.val * (2 * Real.pi) / n = _
    rw [show (E.prescribed.array (regularSites n (2 * Real.pi) a) hx).offset = a from ho]

end TimeTraps.Spectral
