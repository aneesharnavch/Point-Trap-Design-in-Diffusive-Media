module

public import TimeTraps.Spectral.StrengthRootComparison
public import TimeTraps.Spectral.ArctanSplitting

@[expose] public section

/-! Split any chosen strength, preserving the total and allowing the new
interaction its own independently optimized position. -/

namespace TimeTraps.Spectral

open scoped BigOperators

variable {n : ℕ}

noncomputable def splitStrength (x : Fin n → ℝ) (j : Fin n) (a b : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (Function.update x j a) b

theorem splitStrength_castSucc (x : Fin n → ℝ) (j i : Fin n) (a b : ℝ) :
    splitStrength x j a b i.castSucc = Function.update x j a i := Fin.snoc_castSucc _ _ _

theorem splitStrength_last (x : Fin n → ℝ) (j : Fin n) (a b : ℝ) :
    splitStrength x j a b (Fin.last n) = b := Fin.snoc_last _ _

theorem splitStrength_map_sum (f : ℝ → ℝ) (x : Fin n → ℝ) (j : Fin n) (a b : ℝ) :
    (∑ i, f (splitStrength x j a b i)) = (∑ i, f (x i)) - f (x j) + f a + f b := by
  have hp (i : Fin n) : f (Function.update x j a i) =
      f (x i) + if i = j then f a - f (x j) else 0 := by
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi]
  rw [Fin.sum_univ_castSucc]
  simp_rw [splitStrength_castSucc, splitStrength_last]
  calc
    (∑ i, f (Function.update x j a i)) + f b =
        (∑ i, f (x i)) + (f a - f (x j)) + f b := by
      simp_rw [hp]
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by ring

theorem splitStrength_pos (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (j : Fin n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ∀ i, 0 < splitStrength x j a b i := by
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [splitStrength_last]
    exact hb
  · rw [splitStrength_castSucc]
    by_cases hk : k = j
    · subst k
      simpa using ha
    · rw [Function.update_of_ne hk]
      exact hx k

theorem splitStrength_sum (x : Fin n → ℝ) (j : Fin n) {a b : ℝ} (hab : a + b = x j) :
    (∑ i, splitStrength x j a b i) = ∑ i, x i := by
  have h := splitStrength_map_sum id x j a b
  change (∑ i, splitStrength x j a b i) = (∑ i, x i) - x j + a + b at h
  linarith

noncomputable def PlacementProblem.split (C : PlacementProblem n) (j : Fin n)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : PlacementProblem (n + 1) where
  count_pos := Nat.succ_pos n
  length := C.length
  length_pos := C.length_pos
  diffusivity := C.diffusivity
  diffusivity_pos := C.diffusivity_pos
  strength := splitStrength C.strength j a b
  strength_pos := splitStrength_pos C.strength C.strength_pos j ha hb

theorem PlacementProblem.split_root_lt (C : PlacementProblem n) (j : Fin n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = C.strength j) :
    C.root < (C.split j a b ha hb).root := by
  apply C.root_lt_of_phase_sum_lt (C.split j a b ha hb) rfl
  intro k hk
  have hc : 0 < 2 * C.diffusivity * k := mul_pos (mul_pos (by norm_num) C.diffusivity_pos) hk
  have hs := scaledArctan_split_lt hc ha hb
  rw [hab] at hs
  have ht := splitStrength_map_sum (scaledArctan (2 * C.diffusivity * k)) C.strength j a b
  change (∑ i, scaledArctan (2 * C.diffusivity * k) (C.strength i)) <
    ∑ i, scaledArctan (2 * C.diffusivity * k) (splitStrength C.strength j a b i)
  rw [ht]
  linarith

theorem PlacementProblem.split_optimal_value_lt (C : PlacementProblem n) (j : Fin n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = C.strength j) :
    C.optimalPhysical.principalValue < (C.split j a b ha hb).optimalPhysical.principalValue := by
  rw [C.optimal_principalValue, (C.split j a b ha hb).optimal_principalValue]
  change C.diffusivity * C.root ^ 2 < C.diffusivity * (C.split j a b ha hb).root ^ 2
  apply mul_lt_mul_of_pos_left _ C.diffusivity_pos
  nlinarith [C.split_root_lt j ha hb hab, C.root_pos, (C.split j a b ha hb).root_pos]

end TimeTraps.Spectral
