module

public import TimeTraps.Analysis.GraphShiftedContactHeatOrderPositive
public import TimeTraps.Spectral.CompactInverseResolventEuler
public import TimeTraps.Analysis.LpLimitNonnegative

@[expose] public section

/-! The actual mass-shifted graph heat semigroup preserves edgewise L2
nonnegativity and order. Positive resolvent powers converge strongly to
the actual heat family, and nonnegativity passes to each edge L2 limit.
No bound by one, Markov property, or kernel interpretation is asserted. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolvent_pow_nonneg_ae (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (n : ℕ) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (((P.shiftedHeatResolvent s) ^ n) f e) x := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hf
  | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp] using
        P.shiftedHeatResolvent_nonneg_ae s (((P.shiftedHeatResolvent s) ^ n) f) ih

theorem GraphShiftedContactOperatorProblem.shiftedHeatResolvent_euler_tendsto (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (f : GraphL2Product P.geometry) :
    Tendsto (fun n : ℕ => ((P.shiftedHeatResolvent (t / (n : ℝ≥0))) ^ n) f)
      atTop (𝓝 (P.shiftedHeatSemigroup t f)) :=
  P.operatorCompactPositiveInverse.resolvent_euler_tendsto t f

theorem GraphShiftedContactOperatorProblem.shiftedHeatSemigroup_nonneg_ae (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (P.shiftedHeatSemigroup t f e) x := by
  intro e
  apply ae_nonnegative_of_L2_tendsto
    (fun n : ℕ => ((P.shiftedHeatResolvent (t / (n : ℝ≥0))) ^ n) f e) (P.shiftedHeatSemigroup t f e)
  · exact ((graphL2ComponentL P.geometry e).continuous.tendsto _).comp
      (P.shiftedHeatResolvent_euler_tendsto t f)
  · intro n
    exact P.shiftedHeatResolvent_pow_nonneg_ae (t / (n : ℝ≥0)) n f hf e

theorem GraphShiftedContactOperatorProblem.shiftedHeatSemigroup_mono_ae (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (f g : GraphL2Product P.geometry)
    (hfg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ (g e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      (P.shiftedHeatSemigroup t f e) x ≤ (P.shiftedHeatSemigroup t g e) x := by
  have hp : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ ((g - f) e) x := by
    intro e
    simp only [PiLp.sub_apply]
    filter_upwards [hfg e, Lp.coeFn_sub (g e) (f e)] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  intro e
  have hi := P.shiftedHeatSemigroup_nonneg_ae t (g - f) hp e
  rw [map_sub] at hi
  simp only [PiLp.sub_apply] at hi
  filter_upwards [hi, Lp.coeFn_sub (P.shiftedHeatSemigroup t g e) (P.shiftedHeatSemigroup t f e)] with x hx he
  apply sub_nonneg.mp
  simpa only [he, Pi.sub_apply] using hx

end TimeTraps.Analysis
