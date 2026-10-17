module

public import TimeTraps.Probability.GraphPointLocalTimeMartingaleData
public import TimeTraps.Probability.GraphPointLocalTimeMartingaleObservation
public import TimeTraps.Probability.GraphConservativeOccupationTerminal

@[expose] public section

/-! Actual L2 versions of the point-local-time terminal process and its
occupation martingale approximants. Both summands converge in the same
path-law L2 space, with their literal random-variable identifications. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeTerminalL2
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H t : ℝ≥0) : Lp ℝ 2 (P.continuousPathLaw hκ x) :=
  P.pointLocalTimeL2 hκ x a (min t H) + P.pointMartingaleObservationL2 hκ x (min t H)
    (P.pointMartingalePotentialState a (H.val - (min t H).val))

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeTerminalApproxL2
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H t : ℝ≥0) (n : ℕ) : Lp ℝ 2 (P.continuousPathLaw hκ x) :=
  P.occupationL2 hκ x (P.geometry.pointBump a (1 / ((n : ℝ) + 1))) (min t H) +
    P.pointMartingaleObservationL2 hκ x (min t H)
      (P.occupationPotential (P.geometry.pointBump a (1 / ((n : ℝ) + 1))) (H.val - (min t H).val))

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalL2_coe
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H t : ℝ≥0) :
    P.pointLocalTimeTerminalL2 hκ x a H t =ᵐ[P.continuousPathLaw hκ x] P.pointLocalTimeTerminalProcess a H t := by
  filter_upwards [Lp.coeFn_add (P.pointLocalTimeL2 hκ x a (min t H))
      (P.pointMartingaleObservationL2 hκ x (min t H) (P.pointMartingalePotentialState a (H.val - (min t H).val))),
    P.pointLocalTime_eq_L2_ae hκ x a (min t H),
    P.pointMartingaleObservationL2_coe hκ x (min t H) (P.pointMartingalePotentialState a (H.val - (min t H).val))]
    with p hs hl hq
  change (P.pointLocalTimeL2 hκ x a (min t H) +
    P.pointMartingaleObservationL2 hκ x (min t H) (P.pointMartingalePotentialState a (H.val - (min t H).val))) p = _
  rw [hs]
  change P.pointLocalTimeL2 hκ x a (min t H) p +
    P.pointMartingaleObservationL2 hκ x (min t H) (P.pointMartingalePotentialState a (H.val - (min t H).val)) p = _
  rw [← hl, hq]
  rfl

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H t : ℝ≥0) :
    MemLp (P.pointLocalTimeTerminalProcess a H t) 2 (P.continuousPathLaw hκ x) :=
  (Lp.memLp (P.pointLocalTimeTerminalL2 hκ x a H t)).ae_eq (P.pointLocalTimeTerminalL2_coe hκ x a H t)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalApproxL2_coe
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H t : ℝ≥0) (n : ℕ) :
    P.pointLocalTimeTerminalApproxL2 hκ x a H t n =ᵐ[P.continuousPathLaw hκ x]
      P.occupationTerminalProcess (P.geometry.pointBump a (1 / ((n : ℝ) + 1))) H t := by
  let f := P.geometry.pointBump a (1 / ((n : ℝ) + 1))
  filter_upwards [Lp.coeFn_add (P.occupationL2 hκ x f (min t H))
      (P.pointMartingaleObservationL2 hκ x (min t H) (P.occupationPotential f (H.val - (min t H).val))),
    P.occupationL2_coe hκ x f (min t H),
    P.pointMartingaleObservationL2_coe hκ x (min t H) (P.occupationPotential f (H.val - (min t H).val))]
    with p hs hl hq
  change (P.occupationL2 hκ x f (min t H) +
    P.pointMartingaleObservationL2 hκ x (min t H) (P.occupationPotential f (H.val - (min t H).val))) p = _
  rw [hs]
  change P.occupationL2 hκ x f (min t H) p +
    P.pointMartingaleObservationL2 hκ x (min t H) (P.occupationPotential f (H.val - (min t H).val)) p = _
  rw [hl, hq]
  rfl

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalApproxL2_tendsto
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H t : ℝ≥0) :
    Tendsto (P.pointLocalTimeTerminalApproxL2 hκ x a H t) atTop
      (𝓝 (P.pointLocalTimeTerminalL2 hκ x a H t)) := by
  have hU := P.pointMartingalePotentialState_tendsto a
    (T := H.val - (min t H).val) (sub_nonneg.mpr (show (min t H).val ≤ H.val from min_le_right t H))
    (r := fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hQ := (P.pointMartingaleObservationL2_continuous hκ x (min t H)).continuousAt.tendsto.comp hU
  exact (P.pointLocalTimeL2_tendsto hκ x a (min t H)).add hQ

end TimeTraps.Analysis
