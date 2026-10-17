module

public import TimeTraps.Probability.ReflectedContinuousDynkinData
public import TimeTraps.Probability.BrownianJointMeasurability

@[expose] public section

/-! The literal backward heat observable, stopped at a fixed terminal
horizon. The actual reflected Feller operator uses variance 2D times
remaining physical time. Its bound, raw adaptation and path continuity
are properties of this very expression, without changing representatives. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedFellerTimeOperator_comp_nonneg (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerTimeOperator L hL D a (reflectedFellerTimeOperator L hL D b f) =
      reflectedFellerTimeOperator L hL D (a + b) f := by
  have h := congrArg (fun Q : C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) => Q f)
    (reflectedFellerOperator_comp L hL (Real.toNNReal (2 * D * a)) (Real.toNNReal (2 * D * b)))
  change reflectedFellerOperator L hL (Real.toNNReal (2 * D * a))
      (reflectedFellerOperator L hL (Real.toNNReal (2 * D * b)) f) =
    reflectedFellerOperator L hL (Real.toNNReal (2 * D * a) + Real.toNNReal (2 * D * b)) f at h
  rw [← Real.toNNReal_add (mul_nonneg (by positivity) ha) (mul_nonneg (by positivity) hb),
    ← mul_add] at h
  exact h

def reflectedBackwardHeat {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ))
    (T t : ℝ≥0) (ω : Ω) : ℝ :=
  reflectedContinuousInput L hL D x
    (reflectedFellerTimeOperator L hL D (T.val - (min t T).val) f) (B (min t T) ω)

theorem reflectedBackwardHeat_physical {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T t : ℝ≥0) (ω : Ω) :
    reflectedBackwardHeat B L hL D x f T t ω =
      reflectedFellerTimeOperator L hL D (T.val - (min t T).val) f
        ⟨foldedTrajectory L D x B (min t T) ω, foldedTrajectory_mem L hL D x B (min t T) ω⟩ := rfl

theorem reflectedBackwardHeat_after_horizon {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ))
    {T t : ℝ≥0} (hTt : T ≤ t) (ω : Ω) :
    reflectedBackwardHeat B L hL D x f T t ω =
      f ⟨foldedTrajectory L D x B T ω, foldedTrajectory_mem L hL D x B T ω⟩ := by
  rw [reflectedBackwardHeat_physical, min_eq_right hTt, sub_self]
  simp only [reflectedFellerTimeOperator, mul_zero, Real.toNNReal_zero, reflectedFellerOperator_zero]

theorem reflectedBackwardHeat_terminal {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) (ω : Ω) :
    reflectedBackwardHeat B L hL D x f T T ω =
      f ⟨foldedTrajectory L D x B T ω, foldedTrajectory_mem L hL D x B T ω⟩ :=
  reflectedBackwardHeat_after_horizon B L hL D x f le_rfl ω

theorem reflectedBackwardHeat_bound {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T t : ℝ≥0) (ω : Ω) :
    |reflectedBackwardHeat B L hL D x f T t ω| ≤ ‖f‖ :=
  reflectedContinuousInput_time_bound L hL D x f _ _

theorem reflectedBackwardHeat_stronglyAdapted {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    StronglyAdapted (brownianNaturalFiltration B hBm) (reflectedBackwardHeat B L hL D x f T) := by
  intro t
  exact (reflectedContinuousInput_continuous L hL D x _).comp_stronglyMeasurable
    ((brownianNaturalFiltration_stronglyAdapted B hBm (min t T)).mono
      ((brownianNaturalFiltration B hBm).mono (min_le_left t T)))

theorem reflectedBackwardHeat_memLp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) {P : Measure Ω} [IsFiniteMeasure P]
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T t : ℝ≥0) :
    MemLp (reflectedBackwardHeat B L hL D x f T t) 2 P :=
  MemLp.of_bound (((reflectedBackwardHeat_stronglyAdapted B hBm L hL D x f T t).mono
    ((brownianNaturalFiltration B hBm).le t)).aestronglyMeasurable) ‖f‖
    (Eventually.of_forall (reflectedBackwardHeat_bound B L hL D x f T t))

theorem reflectedBackwardHeat_continuous {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ))
    (T : ℝ≥0) (ω : Ω) (hpath : Continuous (fun t => B t ω)) :
    Continuous (fun t => reflectedBackwardHeat B L hL D x f T t ω) := by
  have htime : Continuous (fun t : ℝ≥0 => T.val - (min t T).val) :=
    continuous_const.sub (continuous_subtype_val.comp (continuous_id.min continuous_const))
  have hstate : Continuous (fun t : ℝ≥0 => B (min t T) ω) :=
    hpath.comp (continuous_id.min continuous_const)
  have hc := (reflectedContinuousInput_time_continuous L hL D x f).comp (htime.prodMk hstate)
  simpa only [Function.comp_def, reflectedBackwardHeat] using hc

theorem reflectedBackwardHeat_jointly_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (B : ℝ≥0 → Ω → ℝ) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × Ω => reflectedBackwardHeat B L hL D x f T p.1 p.2) := by
  have htime : Measurable (fun p : ℝ≥0 × Ω => T.val - (min p.1 T).val) := by fun_prop
  have hstate : Measurable (fun p : ℝ≥0 × Ω => B (min p.1 T) p.2) :=
    hjoint.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hm := (reflectedContinuousInput_time_continuous L hL D x f).measurable.comp (htime.prodMk hstate)
  simpa only [Function.comp_def, reflectedBackwardHeat] using hm

end TimeTraps.Probability

end
