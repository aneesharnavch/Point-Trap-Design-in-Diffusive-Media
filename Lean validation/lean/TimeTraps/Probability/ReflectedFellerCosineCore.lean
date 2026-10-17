module

public import TimeTraps.Probability.ReflectedFellerCosine
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Actual Feller evolution and infinitesimal action on the finite
Neumann cosine span. Physical time uses variance `2Dt`; the derivative is
taken in the uniform norm from nonnegative times. This proves membership
and action on the finite span, not equality with the full generator domain. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedFellerOperator_cosine_time (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    reflectedFellerOperator L hL (Real.toNNReal (2 * D * t)) (neumannCosine L n) =
      Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * t) • neumannCosine L n := by
  rw [reflectedFellerOperator_cosine, Real.coe_toNNReal _ (by positivity)]
  congr 1
  congr 1
  ring

theorem reflectedFellerOperator_finite_cosine_time (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    reflectedFellerOperator L hL (Real.toNNReal (2 * D * t))
        (∑ n ∈ s, c n • neumannCosine L n) =
      ∑ n ∈ s, (c n * Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * t)) • neumannCosine L n := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul, reflectedFellerOperator_cosine_time L hL D hD n t ht, smul_smul]

theorem reflectedFellerOperator_cosine_derivative (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r : ℝ =>
      reflectedFellerOperator L hL (Real.toNNReal (2 * D * r)) (neumannCosine L n))
      ((Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * t) *
        (-D * ((n : ℝ) * Real.pi / L) ^ 2)) • neumannCosine L n) (Ici 0) t := by
  have hd := (((hasDerivAt_id t).const_mul (-D * ((n : ℝ) * Real.pi / L) ^ 2)).exp.smul_const
    (neumannCosine L n))
  simp only [id_eq, mul_one] at hd
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro r hr
    exact reflectedFellerOperator_cosine_time L hL D hD n r hr
  · exact ht

theorem reflectedFellerOperator_finite_cosine_generator (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (s : Finset ℕ) (c : ℕ → ℝ) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerOperator L hL (Real.toNNReal (2 * D * t))
      (∑ n ∈ s, c n • neumannCosine L n))
      (∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) • neumannCosine L n) (Ici 0) 0 := by
  have hd (n : ℕ) := (reflectedFellerOperator_cosine_derivative L hL D hD n 0 le_rfl).const_smul (c n)
  simpa only [Pi.smul_apply, mul_zero, Real.exp_zero, one_mul, map_sum, map_smul, smul_smul] using
    (HasDerivWithinAt.fun_sum (fun n (_ : n ∈ s) => hd n))

theorem reflectedFellerOperator_finite_generator_limit (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (s : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ •
      (reflectedFellerOperator L hL (Real.toNNReal (2 * D * t))
        (∑ n ∈ s, c n • neumannCosine L n) - ∑ n ∈ s, c n • neumannCosine L n))
      (𝓝[>] 0) (𝓝 (∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) • neumannCosine L n)) := by
  have hd := hasDerivWithinAt_iff_tendsto_slope.mp
    (reflectedFellerOperator_finite_cosine_generator L hL D hD s c)
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext r
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, ne_of_gt h⟩⟩
  rw [hs] at hd
  apply hd.congr'
  filter_upwards [] with t
  rw [slope_def_module, sub_zero, mul_zero, Real.toNNReal_zero, reflectedFellerOperator_zero]

theorem reflectedFellerOperator_cosineSpan_generator (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) {f : C(Icc (0 : ℝ) L, ℝ)}
    (hf : f ∈ Submodule.span ℝ (Set.range (fun n : ℕ => neumannCosine L n))) :
    ∃ g ∈ Submodule.span ℝ (Set.range (fun n : ℕ => neumannCosine L n)),
      HasDerivWithinAt (fun t : ℝ => reflectedFellerOperator L hL (Real.toNNReal (2 * D * t)) f)
        g (Ici 0) 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, rfl⟩ := hf
    refine ⟨(-D * ((n : ℝ) * Real.pi / L) ^ 2) • neumannCosine L n,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩), ?_⟩
    simpa only [mul_zero, Real.exp_zero, one_mul] using
      reflectedFellerOperator_cosine_derivative L hL D hD n 0 le_rfl
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simpa only [map_zero] using (hasDerivWithinAt_const (0 : ℝ) (Ici 0)
      (0 : C(Icc (0 : ℝ) L, ℝ)))
  | add f g _ _ hf hg =>
    obtain ⟨u, hu, hdu⟩ := hf
    obtain ⟨v, hv, hdv⟩ := hg
    refine ⟨u + v, Submodule.add_mem _ hu hv, ?_⟩
    simpa only [map_add] using hdu.fun_add hdv
  | smul r f _ hf =>
    obtain ⟨u, hu, hdu⟩ := hf
    refine ⟨r • u, Submodule.smul_mem _ r hu, ?_⟩
    simpa only [map_smul] using hdu.fun_const_smul r

end TimeTraps.Probability
