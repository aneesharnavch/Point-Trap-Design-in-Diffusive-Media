module

public import TimeTraps.Analysis.GraphHeatPointPotentialBump
public import TimeTraps.Analysis.GraphHeatPointPotentialJoint

@[expose] public section

/-! Continuous normalized tents approximate each actual point potential
uniformly over an entire compact time interval and both graph points.
The normalization is the original ordinary-length integral. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable def GraphShiftedContactOperatorProblem.bumpPointPotential
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (r : ℝ)
    (x : GraphRealization P.geometry) (t : ℝ) : ℝ :=
  ∫ z, P.realizedHeatPointPotential x z t * P.geometry.pointBump a r z ∂P.geometry.lengthMeasure

theorem GraphShiftedContactOperatorProblem.bumpPointPotential_integrable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (r : ℝ)
    (x : GraphRealization P.geometry) (t : ℝ) :
    Integrable (fun z => P.realizedHeatPointPotential x z t * P.geometry.pointBump a r z)
      P.geometry.lengthMeasure := by
  have hg : Continuous (fun z : GraphRealization P.geometry => ((x, z), t)) :=
    (continuous_const.prodMk continuous_id).prodMk continuous_const
  have hc := P.realizedHeatPointPotential_joint_continuous.comp hg
  exact (hc.mul (P.geometry.pointBump a r).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem GraphShiftedContactOperatorProblem.bumpPointPotential_error
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    {r : ℝ} (hr : 0 < r) (x : GraphRealization P.geometry) (t ε : ℝ)
    (hb : ∀ z ∈ Metric.ball a r,
      |P.realizedHeatPointPotential x z t - P.realizedHeatPointPotential x a t| ≤ ε) :
    |P.bumpPointPotential a r x t - P.realizedHeatPointPotential x a t| ≤ ε := by
  have hi := P.bumpPointPotential_integrable a r x t
  have hw := P.geometry.pointBump_integrable a r
  have he : P.bumpPointPotential a r x t - P.realizedHeatPointPotential x a t =
      ∫ z, (P.realizedHeatPointPotential x z t - P.realizedHeatPointPotential x a t) *
        P.geometry.pointBump a r z ∂P.geometry.lengthMeasure := by
    simp_rw [sub_mul]
    rw [integral_sub hi (hw.const_mul _), integral_const_mul, P.geometry.pointBump_integral_one, mul_one]
    rfl
  rw [he, ← Real.norm_eq_abs]
  have hbound : ∀ᵐ z ∂P.geometry.lengthMeasure,
      ‖(P.realizedHeatPointPotential x z t - P.realizedHeatPointPotential x a t) *
        P.geometry.pointBump a r z‖ ≤ ε * P.geometry.pointBump a r z := by
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : P.geometry.pointBump a r z = 0
    · simp only [hz, mul_zero, norm_zero, le_refl]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (P.geometry.pointBump_nonneg a z r)]
      exact mul_le_mul_of_nonneg_right
        (hb z (P.geometry.pointBump_support_subset a hr hz))
        (P.geometry.pointBump_nonneg a z r)
  have h := norm_integral_le_of_norm_le (hw.const_mul ε) hbound
  simpa only [integral_const_mul, P.geometry.pointBump_integral_one, mul_one] using h

theorem GraphShiftedContactOperatorProblem.bumpPointPotential_compact_uniform
    (P : GraphShiftedContactOperatorProblem V E) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℝ), 0 < r → r < δ →
      ∀ (t : ℝ), t ∈ Icc 0 T → ∀ (x a : GraphRealization P.geometry),
        |P.bumpPointPotential a r x t - P.realizedHeatPointPotential x a t| < ε := by
  obtain ⟨δ, hδ, hb⟩ := Metric.uniformContinuous_iff.mp
    (P.realizedHeatPointPotential_compact_uniformContinuous T) (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ t ht x a
  have hpoint (z : GraphRealization P.geometry) (hz : z ∈ Metric.ball a r) :
      |P.realizedHeatPointPotential x z t - P.realizedHeatPointPotential x a t| ≤ ε / 2 := by
    have hza : dist z a < δ := hz.trans hrδ
    have hpair : dist ((⟨t, ht⟩ : Icc (0 : ℝ) T), (x, z))
        ((⟨t, ht⟩ : Icc (0 : ℝ) T), (x, a)) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hza
    have h := hb hpair
    simpa only [Real.dist_eq] using h.le
  exact (P.bumpPointPotential_error a hr x t (ε / 2) hpoint).trans_lt (by linarith)

end TimeTraps.Analysis
