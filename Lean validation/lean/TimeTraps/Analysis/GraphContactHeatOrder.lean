module

public import TimeTraps.Analysis.GraphContactHeatOrderPositive
public import TimeTraps.Spectral.CompactInverseResolventEuler
public import TimeTraps.Analysis.LpLimitNonnegative

@[expose] public section

/-! The original network heat semigroup preserves edgewise L2
nonnegativity and order. Positive resolvent powers converge strongly to
the actual heat family, and nonnegativity passes to each edge L2 limit.
No bound by one, Markov property, or kernel interpretation is asserted. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphContactOperatorProblem.heatResolvent_pow_nonneg_ae (P : GraphContactOperatorProblem V E)
    (s : ℝ≥0) (n : ℕ) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (((P.heatResolvent s) ^ n) f e) x := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hf
  | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp] using
        P.heatResolvent_nonneg_ae s (((P.heatResolvent s) ^ n) f) ih

theorem GraphContactOperatorProblem.heatResolvent_euler_tendsto (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (f : GraphL2Product P.geometry) :
    Tendsto (fun n : ℕ => ((P.heatResolvent (t / (n : ℝ≥0))) ^ n) f)
      atTop (𝓝 (P.heatSemigroup t f)) :=
  P.operatorCompactPositiveInverse.resolvent_euler_tendsto t f

theorem GraphContactOperatorProblem.heatSemigroup_nonneg_ae (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (f : GraphL2Product P.geometry)
    (hf : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (f e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ (P.heatSemigroup t f e) x := by
  intro e
  apply ae_nonnegative_of_L2_tendsto
    (fun n : ℕ => ((P.heatResolvent (t / (n : ℝ≥0))) ^ n) f e) (P.heatSemigroup t f e)
  · exact ((graphL2ComponentL P.geometry e).continuous.tendsto _).comp
      (P.heatResolvent_euler_tendsto t f)
  · intro n
    exact P.heatResolvent_pow_nonneg_ae (t / (n : ℝ≥0)) n f hf e

theorem GraphContactOperatorProblem.heatSemigroup_mono_ae (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (f g : GraphL2Product P.geometry)
    (hfg : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), (f e) x ≤ (g e) x) :
    ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)),
      (P.heatSemigroup t f e) x ≤ (P.heatSemigroup t g e) x := by
  have hp : ∀ e, ∀ᵐ x ∂volume.restrict (Ioo 0 (P.geometry.length e)), 0 ≤ ((g - f) e) x := by
    intro e
    simp only [PiLp.sub_apply]
    filter_upwards [hfg e, Lp.coeFn_sub (g e) (f e)] with x hx he
    simpa only [he, Pi.sub_apply] using sub_nonneg.mpr hx
  intro e
  have hi := P.heatSemigroup_nonneg_ae t (g - f) hp e
  rw [map_sub] at hi
  simp only [PiLp.sub_apply] at hi
  filter_upwards [hi, Lp.coeFn_sub (P.heatSemigroup t g e) (P.heatSemigroup t f e)] with x hx he
  apply sub_nonneg.mp
  simpa only [he, Pi.sub_apply] using hx

end TimeTraps.Analysis
