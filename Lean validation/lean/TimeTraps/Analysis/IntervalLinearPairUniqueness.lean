module

public import TimeTraps.Analysis.IntervalLinearPairField

@[expose] public section

/-! Zero Cauchy data force an actual AC state/flux pair to vanish on
the entire closed interval for arbitrary continuous variable coefficients.
The AE system is upgraded by continuity of its right-hand side; endpoint
and interior initial data are all included. -/

noncomputable section

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology NNReal

theorem intervalEnergy_pair_eq_zero_of_cauchy
    {u j q c : ℝ → ℝ} {a b t₀ : ℝ}
    (hu : IntervalEnergy u a b) (hj : IntervalEnergy j a b)
    (hq : ContinuousOn q (Icc a b)) (hc : ContinuousOn c (Icc a b))
    (hdu : deriv u =ᵐ[volume.restrict (Ioo a b)] (fun x => q x * j x))
    (hdj : deriv j =ᵐ[volume.restrict (Ioo a b)] (fun x => c x * u x))
    (hab : a < b) (ht₀ : t₀ ∈ Icc a b) (hu₀ : u t₀ = 0) (hj₀ : j t₀ = 0) :
    ∀ x ∈ Icc a b, u x = 0 ∧ j x = 0 := by
  let A := intervalLinearPairField q c
  let f : ℝ → ℝ × ℝ := fun x => (u x, j x)
  have huc : ContinuousOn u (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hu.continuousOn
  have hjc : ContinuousOn j (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hj.continuousOn
  have hqj : ContinuousOn (fun x => q x * j x) (Icc a b) := hq.mul hjc
  have hcu : ContinuousOn (fun x => c x * u x) (Icc a b) := hc.mul huc
  have hfc : ContinuousOn f (Icc a b) := huc.prodMk hjc
  have hfd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt f (A x (f x)) x := by
    change HasDerivAt (fun x => (u x, j x)) (q x * j x, c x * u x) x
    exact (intervalEnergy_hasDerivAt_of_ae_deriv hu hqj hdu hx).prodMk
      (intervalEnergy_hasDerivAt_of_ae_deriv hj hcu hdj hx)
  have hfl : HasDerivWithinAt f (A a (f a)) (Ici a) a := by
    change HasDerivWithinAt (fun x => (u x, j x)) (q a * j a, c a * u a) (Ici a) a
    exact (intervalEnergy_hasDerivWithinAt_left_of_ae_deriv hu hab hqj hdu).prodMk
      (intervalEnergy_hasDerivWithinAt_left_of_ae_deriv hj hab hcu hdj)
  have hfr : HasDerivWithinAt f (A b (f b)) (Iic b) b := by
    change HasDerivWithinAt (fun x => (u x, j x)) (q b * j b, c b * u b) (Iic b) b
    exact (intervalEnergy_hasDerivWithinAt_right_of_ae_deriv hu hab hqj hdu).prodMk
      (intervalEnergy_hasDerivWithinAt_right_of_ae_deriv hj hab hcu hdj)
  obtain ⟨K, hK⟩ := intervalLinearPairField_lipschitz hq hc
  have hz : f t₀ = (0 : ℝ × ℝ) := Prod.ext hu₀ hj₀
  have he : EqOn f (fun _ => (0 : ℝ × ℝ)) (Icc a b) := by
    by_cases hl : t₀ = a
    · subst t₀
      apply ODE_solution_unique_of_mem_Icc_right
        (v := fun x => A x) (s := fun _ => univ) (K := K)
        (fun x hx => (hK x ⟨hx.1, hx.2.le⟩).lipschitzOnWith) hfc _ (fun _ _ => mem_univ _)
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
          (v := fun x => A x) (s := fun _ => univ) (K := K)
          (fun x hx => (hK x ⟨hx.1.le, hx.2⟩).lipschitzOnWith) hfc _ (fun _ _ => mem_univ _)
          continuousOn_const _ (fun _ _ => mem_univ _) hz
        · intro x hx
          by_cases hxb : x = b
          · subst x
            exact hfr
          · exact (hfd x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩).hasDerivWithinAt
        · intro x _
          simpa only [map_zero] using (hasDerivAt_const x (0 : ℝ × ℝ)).hasDerivWithinAt
      · apply ODE_solution_unique_of_mem_Icc
          (v := fun x => A x) (s := fun _ => univ) (K := K)
          (fun x hx => (hK x (Ioo_subset_Icc_self hx)).lipschitzOnWith)
          ⟨lt_of_le_of_ne ht₀.1 (Ne.symm hl), lt_of_le_of_ne ht₀.2 hr⟩
          hfc hfd (fun _ _ => mem_univ _) continuousOn_const _ (fun _ _ => mem_univ _) hz
        intro x _
        simpa only [map_zero] using hasDerivAt_const x (0 : ℝ × ℝ)
  intro x hx
  exact ⟨congrArg Prod.fst (he hx), congrArg Prod.snd (he hx)⟩

end TimeTraps.Analysis

end
