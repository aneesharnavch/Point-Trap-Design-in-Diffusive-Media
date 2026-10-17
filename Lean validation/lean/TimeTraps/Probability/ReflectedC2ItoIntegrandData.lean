module

public import TimeTraps.Probability.ReflectedContinuousDynkinData
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! The actual derivative process F'(X_t) for a globally C² test and
the folded Brownian trajectory. Its bound comes from the derivative's
uniform norm on [0,L], with no global derivative bound or Neumann condition. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def reflectedC2DerivativeMap {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun y => deriv F y.val, (hF.continuous_deriv (by norm_num)).comp continuous_subtype_val⟩

def reflectedC2DerivativeBound {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) : ℝ≥0 :=
  ‖reflectedC2DerivativeMap hF L‖₊

def reflectedC2DerivativeProcess (F : ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (L D x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  deriv F (foldedTrajectory L D x B t ω)

theorem reflectedC2DerivativeProcess_stronglyAdapted {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hBm : ∀ t, Measurable (B t)) (L D x : ℝ) (t : ℝ≥0) :
    StronglyMeasurable[brownianNaturalFiltration B hBm t] (reflectedC2DerivativeProcess F B L D x t) := by
  have hc : Continuous (fun z : ℝ => deriv F (reflectedFold L (x + Real.sqrt (2 * D) * z))) :=
    (hF.continuous_deriv (by norm_num)).comp ((reflectedFold_continuous L).comp (by fun_prop))
  exact hc.comp_stronglyMeasurable (brownianNaturalFiltration_stronglyAdapted B hBm t)

theorem reflectedC2DerivativeProcess_jointlyMeasurable {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (L D x : ℝ) :
    Measurable (fun p : ℝ≥0 × Ω => reflectedC2DerivativeProcess F B L D x p.1 p.2) :=
  (hF.continuous_deriv (by norm_num)).measurable.comp
    (foldedTrajectory_joint_measurable L D x B hjoint)

theorem reflectedC2DerivativeProcess_continuous_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (L D x : ℝ) :
    ∀ᵐ ω ∂P, Continuous (fun t => reflectedC2DerivativeProcess F B L D x t ω) := by
  filter_upwards [hB.cont] with ω hω
  exact (hF.continuous_deriv (by norm_num)).comp
    ((reflectedFold_continuous L).comp (continuous_const.add (continuous_const.mul hω)))

theorem reflectedC2DerivativeProcess_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (B : ℝ≥0 → Ω → ℝ) (L : ℝ) (hL : 0 < L) (D x : ℝ) (t : ℝ≥0) (ω : Ω) :
    |reflectedC2DerivativeProcess F B L D x t ω| ≤ (reflectedC2DerivativeBound hF L).val :=
  (reflectedC2DerivativeMap hF L).norm_coe_le_norm
    ⟨foldedTrajectory L D x B t ω, foldedTrajectory_mem L hL D x B t ω⟩

end TimeTraps.Probability

end
