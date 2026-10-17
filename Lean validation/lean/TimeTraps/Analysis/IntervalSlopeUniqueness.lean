module

public import TimeTraps.Analysis.IntervalSlopeUniquenessRegularity
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! Zero Cauchy data determine the zero solution for the actual AC state
and AC slope satisfying u'' = c u, for every real c. The proof applies
Gronwall uniqueness to the bounded linear vector field (u,j) ↦ (j,c*u).
Initial data may be at either endpoint or anywhere in the interior. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

theorem IntervalSlopeRegularity.eq_zero_of_linear_cauchy
    {u j : ℝ → ℝ} {c a b t₀ : ℝ}
    (h : IntervalSlopeRegularity u j (fun x => c * u x) a b)
    (hab : a < b) (ht₀ : t₀ ∈ Icc a b) (hu₀ : u t₀ = 0) (hj₀ : j t₀ = 0) :
    ∀ x ∈ Icc a b, u x = 0 ∧ j x = 0 := by
  let A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (c • ContinuousLinearMap.fst ℝ ℝ ℝ)
  let f : ℝ → ℝ × ℝ := fun x => (u x, j x)
  have huc : ContinuousOn u (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using h.state_energy.continuousOn
  have hjc : ContinuousOn j (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using h.slope_energy.continuousOn
  have hcu : ContinuousOn (fun x => c * u x) (Icc a b) := continuousOn_const.mul huc
  have hfc : ContinuousOn f (Icc a b) := huc.prodMk hjc
  have hfd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt f (A (f x)) x := by
    change HasDerivAt (fun x => (u x, j x)) (j x, c * u x) x
    exact (h.hasDerivAt hx).prodMk (h.linear_slope_hasDerivAt hx)
  have hfl : HasDerivWithinAt f (A (f a)) (Ici a) a := by
    change HasDerivWithinAt (fun x => (u x, j x)) (j a, c * u a) (Ici a) a
    exact (intervalEnergy_hasDerivWithinAt_left_of_ae_deriv h.state_energy hab hjc h.slope_ae).prodMk
      (intervalEnergy_hasDerivWithinAt_left_of_ae_deriv h.slope_energy hab hcu h.second_ae)
  have hfr : HasDerivWithinAt f (A (f b)) (Iic b) b := by
    change HasDerivWithinAt (fun x => (u x, j x)) (j b, c * u b) (Iic b) b
    exact (intervalEnergy_hasDerivWithinAt_right_of_ae_deriv h.state_energy hab hjc h.slope_ae).prodMk
      (intervalEnergy_hasDerivWithinAt_right_of_ae_deriv h.slope_energy hab hcu h.second_ae)
  have hz : f t₀ = (0 : ℝ × ℝ) := Prod.ext hu₀ hj₀
  have he : EqOn f (fun _ => (0 : ℝ × ℝ)) (Icc a b) := by
    by_cases hl : t₀ = a
    · subst t₀
      apply ODE_solution_unique_of_mem_Icc_right
        (v := fun _ => A) (s := fun _ => univ)
        (fun _ _ => A.lipschitz.lipschitzOnWith) hfc _ (fun _ _ => mem_univ _)
        continuousOn_const _ (fun _ _ => mem_univ _) hz
      · intro x hx
        by_cases hxa : x = a
        · subst x
          exact hfl
        · exact (hfd x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hx.2⟩).hasDerivWithinAt
      · intro x _
        simpa only [map_zero] using (hasDerivAt_const x (0 : ℝ × ℝ)).hasDerivWithinAt
    · by_cases hr : t₀ = b
      · subst t₀
        apply ODE_solution_unique_of_mem_Icc_left
          (v := fun _ => A) (s := fun _ => univ)
          (fun _ _ => A.lipschitz.lipschitzOnWith) hfc _ (fun _ _ => mem_univ _)
          continuousOn_const _ (fun _ _ => mem_univ _) hz
        · intro x hx
          by_cases hxb : x = b
          · subst x
            exact hfr
          · exact (hfd x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩).hasDerivWithinAt
        · intro x _
          simpa only [map_zero] using (hasDerivAt_const x (0 : ℝ × ℝ)).hasDerivWithinAt
      · apply ODE_solution_unique_of_mem_Icc
          (v := fun _ => A) (s := fun _ => univ)
          (fun _ _ => A.lipschitz.lipschitzOnWith)
          ⟨lt_of_le_of_ne ht₀.1 (Ne.symm hl), lt_of_le_of_ne ht₀.2 hr⟩
          hfc hfd (fun _ _ => mem_univ _) continuousOn_const _ (fun _ _ => mem_univ _) hz
        intro x _
        simpa only [map_zero] using hasDerivAt_const x (0 : ℝ × ℝ)
  intro x hx
  exact ⟨congrArg Prod.fst (he hx), congrArg Prod.snd (he hx)⟩

end TimeTraps.Analysis
