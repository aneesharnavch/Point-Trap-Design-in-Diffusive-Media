module

public import TimeTraps.Probability.ReflectedC2ItoIntegrandData
public import TimeTraps.Probability.ReflectedC2ItoDriftMeasurable
public import TimeTraps.Probability.BrownianItoDriftContinuity
public import TimeTraps.Probability.BrownianItoDriftContinuousAdapted

@[expose] public section

/-! The actual curvature drift and values of a globally C² function
along the folded path. All bounds are derived on [0,L]. Curvature is
merely continuous there: no global derivative bound, third derivative,
Neumann condition, or Itô formula is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def reflectedC2ValueMap {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun y => F y.val, hF.continuous.comp continuous_subtype_val⟩

def reflectedC2CurvatureMap {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun y => deriv (deriv F) y.val,
    ((show ContDiff ℝ 1 (deriv F) from hF.deriv').continuous_deriv (by norm_num)).comp continuous_subtype_val⟩

def reflectedC2ItoDrift (F : ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (L D x : ℝ)
    (T : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..T.val, deriv (deriv F) (foldedTrajectory L D x B r.toNNReal ω)

theorem reflectedC2_value_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (B : ℝ≥0 → Ω → ℝ) (L : ℝ) (hL : 0 < L) (D x : ℝ) (t : ℝ≥0) (ω : Ω) :
    |F (foldedTrajectory L D x B t ω)| ≤ ‖reflectedC2ValueMap hF L‖ :=
  (reflectedC2ValueMap hF L).norm_coe_le_norm
    ⟨foldedTrajectory L D x B t ω, foldedTrajectory_mem L hL D x B t ω⟩

theorem reflectedC2_curvature_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (B : ℝ≥0 → Ω → ℝ) (L : ℝ) (hL : 0 < L) (D x : ℝ) (t : ℝ≥0) (ω : Ω) :
    |deriv (deriv F) (foldedTrajectory L D x B t ω)| ≤ ‖reflectedC2CurvatureMap hF L‖ :=
  (reflectedC2CurvatureMap hF L).norm_coe_le_norm
    ⟨foldedTrajectory L D x B t ω, foldedTrajectory_mem L hL D x B t ω⟩

theorem reflectedC2_value_memLp [IsFiniteMeasure P] {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    MemLp (fun ω => F (foldedTrajectory L D x B T ω)) 2 P :=
  MemLp.of_bound (hF.continuous.measurable.comp
    (foldedTrajectory_measurable L D x B hBm T)).aestronglyMeasurable ‖reflectedC2ValueMap hF L‖
      (Eventually.of_forall (reflectedC2_value_bound hF B L hL D x T))

theorem reflectedC2_value_difference_memLp [IsFiniteMeasure P] {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    MemLp (fun ω => F (foldedTrajectory L D x B T ω) - F (reflectedFold L x)) 2 P :=
  (reflectedC2_value_memLp hF hBm L hL D x T).sub (memLp_const _)

theorem reflectedC2ItoDrift_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (B : ℝ≥0 → Ω → ℝ) (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) (ω : Ω) :
    |reflectedC2ItoDrift F B L D x T ω| ≤ T.val * ‖reflectedC2CurvatureMap hF L‖ :=
  brownianItoDrift_bounded_abs
    (reflectedContinuousInput_bound L hL D x (reflectedC2CurvatureMap hF L)) T ω

theorem reflectedC2ItoDrift_memLp [IsFiniteMeasure P] {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    MemLp (reflectedC2ItoDrift F B L D x T) 2 P :=
  brownianItoDrift_bounded_memLp
    (reflectedContinuousInput_continuous L hL D x (reflectedC2CurvatureMap hF L)).measurable
    hjoint (reflectedContinuousInput_bound L hL D x (reflectedC2CurvatureMap hF L)) T

theorem reflectedC2ItoDrift_continuous_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    ∀ᵐ ω ∂P, Continuous (fun t => reflectedC2ItoDrift F B L D x t ω) := by
  filter_upwards [hB.cont] with ω hω
  exact brownianItoDrift_continuous
    (reflectedContinuousInput_continuous L hL D x (reflectedC2CurvatureMap hF L)) hω

theorem reflectedC2ItoDrift_raw_aestronglyMeasurable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm T] (reflectedC2ItoDrift F B L D x T) P :=
  brownianItoDrift_continuous_aestronglyMeasurable_past hB hBm
    (reflectedContinuousInput_continuous L hL D x (reflectedC2CurvatureMap hF L))
    (reflectedContinuousInput_bound L hL D x (reflectedC2CurvatureMap hF L)) T

theorem reflectedC2ItoDrift_jointlyMeasurable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (L D x : ℝ) :
    Measurable (fun p : ℝ≥0 × Ω => reflectedC2ItoDrift F B L D x p.1 p.2) := by
  unfold reflectedC2ItoDrift
  have hc : Continuous (deriv (deriv F)) :=
    (show ContDiff ℝ 1 (deriv F) from hF.deriv').continuous_deriv (by norm_num)
  have hm : Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hx := (foldedTrajectory_joint_measurable L D x B hjoint).comp hm
  have hH := hc.measurable.comp hx
  have hi := timeIntegral_jointlyMeasurable hH
  exact hi

end TimeTraps.Probability

end
