module

public import TimeTraps.Probability.GraphPointLocalTimePath

@[expose] public section

/-! Continuous graph tests evaluated at a deterministic path time give a
continuous map into the actual path-law L2 space. Uniform spatial
convergence can therefore be transported to genuine L2 convergence. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointMartingaleObservation_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (f : C(GraphRealization P.geometry, ℝ)) :
    MemLp (fun p : GraphContinuousPath P.geometry => f (p t)) 2 (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact MemLp.of_bound (f.continuous.comp (continuous_eval_const t)).stronglyMeasurable.aestronglyMeasurable
    ‖f‖ (Eventually.of_forall (fun p => f.norm_coe_le_norm (p t)))

noncomputable def GraphShiftedContactOperatorProblem.pointMartingaleObservationL2
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (f : C(GraphRealization P.geometry, ℝ)) :
    Lp ℝ 2 (P.continuousPathLaw hκ x) :=
  (P.pointMartingaleObservation_memLp hκ x t f).toLp (fun p => f (p t))

theorem GraphShiftedContactOperatorProblem.pointMartingaleObservationL2_coe
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (f : C(GraphRealization P.geometry, ℝ)) :
    P.pointMartingaleObservationL2 hκ x t f =ᵐ[P.continuousPathLaw hκ x] fun p => f (p t) :=
  (P.pointMartingaleObservation_memLp hκ x t f).coeFn_toLp

theorem GraphShiftedContactOperatorProblem.pointMartingaleObservationL2_dist_le
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (f g : C(GraphRealization P.geometry, ℝ)) :
    dist (P.pointMartingaleObservationL2 hκ x t f) (P.pointMartingaleObservationL2 hκ x t g) ≤ dist f g := by
  let inst := P.continuousPathLaw_probability hκ x
  rw [dist_eq_norm, dist_eq_norm]
  have hb : ∀ᵐ p ∂P.continuousPathLaw hκ x,
      ‖(P.pointMartingaleObservationL2 hκ x t f - P.pointMartingaleObservationL2 hκ x t g) p‖ ≤ ‖f - g‖ := by
    filter_upwards [Lp.coeFn_sub (P.pointMartingaleObservationL2 hκ x t f) (P.pointMartingaleObservationL2 hκ x t g),
      P.pointMartingaleObservationL2_coe hκ x t f, P.pointMartingaleObservationL2_coe hκ x t g] with p hs hf hg
    simpa only [hs, Pi.sub_apply, hf, hg, ContinuousMap.sub_apply] using (f - g).norm_coe_le_norm (p t)
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (norm_nonneg (f - g)) hb

theorem GraphShiftedContactOperatorProblem.pointMartingaleObservationL2_continuous
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) :
    Continuous (P.pointMartingaleObservationL2 hκ x t) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [NNReal.coe_one, one_mul] using P.pointMartingaleObservationL2_dist_le hκ x t f g

end TimeTraps.Analysis
