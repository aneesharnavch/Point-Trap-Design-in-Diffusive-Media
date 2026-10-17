module

public import TimeTraps.Probability.ReflectedFellerNeumannIntegral
public import TimeTraps.Probability.ReflectedFellerNeumannData

@[expose] public section

/-! Every full C² Neumann test belongs to the actual reflected Feller
generator domain, with generator D times the classical curvature. The
derivative and difference quotient are in the continuous-function norm.
This is an inclusion theorem, not the converse domain characterization. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped Topology

theorem ReflectedNeumannC2.feller_integral {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 ≤ D) (t : ℝ) (ht : 0 ≤ t) :
    reflectedFellerTimeOperator L hL D t F.valueMap - F.valueMap =
      reflectedFellerIntegralOperator L hL D t (D • F.curvatureMap) := by
  have hk : reflectedFellerNeumannPrimitive L hL F.curvatureMap = F.valueMap - F.value 0 • 1 := by
    rw [reflectedFellerNeumannPrimitive_apply, F.meanZero_curvature hL, F.double_primitive hL]
  have hone : reflectedFellerTimeOperator L hL D t 1 = 1 :=
    reflectedFellerOperator_one L hL _
  have he := reflectedFellerNeumannPrimitive_integral L hL D hD F.curvatureMap t ht
  simpa only [hk, F.meanZero_curvature hL, map_sub, map_smul, hone,
    sub_sub_sub_cancel_right] using he

theorem ReflectedNeumannC2.feller_generator {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 ≤ D) :
    HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t F.valueMap)
      (D • F.curvatureMap) (Ici 0) 0 :=
  reflectedFeller_generator_of_integral L hL D F.valueMap (D • F.curvatureMap)
    (F.feller_integral hL D hD)

theorem ReflectedNeumannC2.feller_evolution_derivative {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 ≤ D) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r : ℝ => reflectedFellerTimeOperator L hL D r F.valueMap)
      (reflectedFellerTimeOperator L hL D t (D • F.curvatureMap)) (Ici 0) t := by
  have hc := reflectedFellerTimeOperator_continuous L hL D (D • F.curvatureMap)
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt (fun r : ℝ => reflectedFellerIntegralOperator L hL D r (D • F.curvatureMap))
    (reflectedFellerTimeOperator L hL D t (D • F.curvatureMap)) t at hd
  apply (hd.add_const F.valueMap).hasDerivWithinAt.congr_of_mem
  · intro r hr
    exact sub_eq_iff_eq_add.mp (F.feller_integral hL D hD r hr)
  · exact ht

theorem ReflectedNeumannC2.feller_generator_limit {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 ≤ D) :
    Tendsto (fun t : ℝ => t⁻¹ • (reflectedFellerTimeOperator L hL D t F.valueMap - F.valueMap))
      (𝓝[>] 0) (𝓝 (D • F.curvatureMap)) := by
  have hd := hasDerivWithinAt_iff_tendsto_slope.mp (F.feller_generator hL D hD)
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext r
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, ne_of_gt h⟩⟩
  rw [hs] at hd
  apply hd.congr'
  filter_upwards [] with t
  rw [slope_def_module, sub_zero]
  simp only [reflectedFellerTimeOperator, mul_zero, Real.toNNReal_zero, reflectedFellerOperator_zero]

theorem ReflectedNeumannC2.feller_spatial_generator {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) :
    ∃ g : C(Icc (0 : ℝ) L, ℝ),
      HasDerivWithinAt (fun t : ℝ => reflectedFellerTimeOperator L hL D t F.valueMap) g (Ici 0) 0 ∧
      ∀ x : Icc (0 : ℝ) L, g x = D * F.curvature x.val :=
  ⟨D • F.curvatureMap, F.feller_generator hL D hD.le, fun _ => rfl⟩

end TimeTraps.Probability
