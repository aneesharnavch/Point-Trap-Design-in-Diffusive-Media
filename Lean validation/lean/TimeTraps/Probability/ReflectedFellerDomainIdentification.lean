module

public import TimeTraps.Probability.ReflectedFellerDomainMoments
public import TimeTraps.Probability.ReflectedFellerDomainSeparation
public import TimeTraps.Probability.ReflectedFellerDomainReconstruction

@[expose] public section

/-! Exact domain equality for the actual reflected Feller generator:
its uniform-norm right derivative exists precisely on the full C²
Neumann class, and is D times the classical second derivative. The
positive diffusivity is used when reconstructing the curvature. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped Topology

theorem reflectedFeller_generator_unique_mean (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f u g : C(Icc (0 : ℝ) L, ℝ))
    (hf : HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0)
    (hu : HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t u) g (Ici 0) 0)
    (hm : reflectedFellerMean L hL f = reflectedFellerMean L hL u) : f = u := by
  apply reflectedFeller_cosine_pairings_separate L hL f u
  intro n
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero, neumannCosine_zero, reflectedFellerPairing_apply, one_mul] using hm
  have ha : -D * ((n : ℝ) * Real.pi / L) ^ 2 ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hD.ne')
      (pow_ne_zero _ (reflectedFeller_cosine_frequency_ne L hL n hn))
  apply mul_left_cancel₀ ha
  exact (reflectedFeller_generator_cosine_moment L hL D hD.le f g hf n).symm.trans
    (reflectedFeller_generator_cosine_moment L hL D hD.le u g hu n)

theorem reflectedFeller_generator_exists_neumannC2 (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f g : C(Icc (0 : ℝ) L, ℝ))
    (hg : HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0) :
    ∃ F : ReflectedNeumannC2 L, F.valueMap = f ∧ D • F.curvatureMap = g := by
  let q := D⁻¹ • g
  have hq : reflectedFellerMean L hL q = 0 := by
    change reflectedFellerMean L hL (D⁻¹ • g) = 0
    rw [map_smul, reflectedFeller_generator_mean_zero L hL D hD.le f g hg, smul_zero]
  let c := reflectedFellerMean L hL f -
    reflectedFellerMean L hL (reflectedFellerPrimitive L hL (reflectedFellerPrimitive L hL q))
  let F := reflectedNeumannOfCurvature L hL q hq c
  have hcurv : D • F.curvatureMap = g := by
    rw [reflectedNeumannOfCurvature_curvature]
    change D • (D⁻¹ • g) = g
    rw [smul_smul, mul_inv_cancel₀ hD.ne', one_smul]
  have hmean : reflectedFellerMean L hL f = reflectedFellerMean L hL F.valueMap := by
    have hsc : reflectedFellerMean L hL (c • 1) = c := by
      rw [map_smul, reflectedFellerMean_one, smul_eq_mul, mul_one]
    rw [reflectedNeumannOfCurvature_value, map_add, hsc]
    dsimp [c]
    ring
  have hF : HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t F.valueMap)
      g (Ici 0) 0 := by
    simpa only [hcurv] using F.feller_generator hL D hD.le
  exact ⟨F, (reflectedFeller_generator_unique_mean L hL D hD f F.valueMap g hg hF hmean).symm, hcurv⟩

theorem reflectedFeller_generator_iff_neumannC2 (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f g : C(Icc (0 : ℝ) L, ℝ)) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0 ↔
      ∃ F : ReflectedNeumannC2 L, F.valueMap = f ∧ D • F.curvatureMap = g := by
  constructor
  · exact reflectedFeller_generator_exists_neumannC2 L hL D hD f g
  · rintro ⟨F, hf, hg⟩
    simpa only [hf, hg] using F.feller_generator hL D hD.le

theorem reflectedFeller_generator_iff_limit (L : ℝ) (hL : 0 < L)
    (D : ℝ) (f g : C(Icc (0 : ℝ) L, ℝ)) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) g (Ici 0) 0 ↔
      Tendsto (fun t : ℝ => t⁻¹ • (reflectedFellerTimeOperator L hL D t f - f))
        (𝓝[>] 0) (𝓝 g) := by
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext r
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, ne_of_gt h⟩⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, hs]
  have he : slope (fun t : ℝ => reflectedFellerTimeOperator L hL D t f) 0 =
      (fun t : ℝ => t⁻¹ • (reflectedFellerTimeOperator L hL D t f - f)) := by
    funext t
    rw [slope_def_module, sub_zero]
    simp only [reflectedFellerTimeOperator, mul_zero, Real.toNNReal_zero, reflectedFellerOperator_zero]
  rw [he]

theorem reflectedFeller_generator_limit_iff_neumannC2 (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f g : C(Icc (0 : ℝ) L, ℝ)) :
    Tendsto (fun t : ℝ => t⁻¹ • (reflectedFellerTimeOperator L hL D t f - f))
      (𝓝[>] 0) (𝓝 g) ↔
      ∃ F : ReflectedNeumannC2 L, F.valueMap = f ∧ D • F.curvatureMap = g := by
  rw [← reflectedFeller_generator_iff_limit, reflectedFeller_generator_iff_neumannC2 L hL D hD]

end TimeTraps.Probability
