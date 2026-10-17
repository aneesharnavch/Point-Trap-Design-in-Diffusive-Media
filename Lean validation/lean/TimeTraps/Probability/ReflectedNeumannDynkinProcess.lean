module

public import TimeTraps.Probability.ReflectedContinuousDynkinData
public import TimeTraps.Probability.ReflectedFellerNeumannData
public import TimeTraps.Probability.BrownianItoDriftContinuousAdapted

@[expose] public section

/-! The literal full C² Neumann Dynkin expression, with its actual
ordinary-time compensator. Curvature is merely continuous on the closed
interval. Raw-past measurability is almost everywhere, using Brownian
path continuity; the physical initial state is retained explicitly. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def reflectedNeumannDynkin {Ω : Type*} {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (B : ℝ≥0 → Ω → ℝ) (D x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  reflectedContinuousInput L hL D x F.valueMap (B t ω) -
    reflectedContinuousInput L hL D x F.valueMap (B 0 ω) -
    D * brownianItoDrift B (reflectedContinuousInput L hL D x F.curvatureMap) t ω

theorem reflectedNeumannDynkin_zero {Ω : Type*} {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (B : ℝ≥0 → Ω → ℝ) (D x : ℝ) (ω : Ω) :
    reflectedNeumannDynkin F hL B D x 0 ω = 0 := by
  simp only [reflectedNeumannDynkin, brownianItoDrift_zero, sub_self, mul_zero]

theorem reflectedNeumannDynkin_physical {Ω : Type*} {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (B : ℝ≥0 → Ω → ℝ) (D x : ℝ) (t : ℝ≥0) (ω : Ω) :
    reflectedNeumannDynkin F hL B D x t ω =
      F.value (foldedTrajectory L D x B t ω) - F.value (foldedTrajectory L D x B 0 ω) -
        D * ∫ r in (0 : ℝ)..t.val, F.curvature (foldedTrajectory L D x B r.toNNReal ω) := rfl

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedContinuousInput_eval_memLp [IsFiniteMeasure P]
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) :
    MemLp (fun ω => reflectedContinuousInput L hL D x f (B t ω)) 2 P :=
  MemLp.of_bound (((reflectedContinuousInput_continuous L hL D x f).measurable.comp
    (hBm t)).aestronglyMeasurable) ‖f‖
    (Eventually.of_forall (fun ω => reflectedContinuousInput_bound L hL D x f (B t ω)))

theorem reflectedNeumannDynkin_memLp [IsFiniteMeasure P] {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (D x : ℝ) (t : ℝ≥0) :
    MemLp (reflectedNeumannDynkin F hL B D x t) 2 P := by
  exact ((reflectedContinuousInput_eval_memLp hBm L hL D x F.valueMap t).sub
    (reflectedContinuousInput_eval_memLp hBm L hL D x F.valueMap 0)).sub
    ((brownianItoDrift_bounded_memLp (reflectedContinuousInput_continuous L hL D x F.curvatureMap).measurable
      hjoint (reflectedContinuousInput_bound L hL D x F.curvatureMap) t).const_mul D)

theorem reflectedNeumannDynkin_aestronglyMeasurable {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (D x : ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm t]
      (reflectedNeumannDynkin F hL B D x t) P := by
  have hg := reflectedContinuousInput_continuous L hL D x F.valueMap
  have ht := hg.comp_stronglyMeasurable (brownianNaturalFiltration_stronglyAdapted B hBm t)
  have h0 := hg.comp_stronglyMeasurable
    ((brownianNaturalFiltration_stronglyAdapted B hBm 0).mono
      ((brownianNaturalFiltration B hBm).mono (show (0 : ℝ≥0) ≤ t from zero_le)))
  exact (ht.sub h0).aestronglyMeasurable.sub
    ((brownianItoDrift_continuous_aestronglyMeasurable_past hB hBm
      (reflectedContinuousInput_continuous L hL D x F.curvatureMap)
      (reflectedContinuousInput_bound L hL D x F.curvatureMap) t).const_mul D)

end TimeTraps.Probability
