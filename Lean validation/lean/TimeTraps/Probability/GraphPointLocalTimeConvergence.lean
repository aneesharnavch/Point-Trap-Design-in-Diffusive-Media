module

public import TimeTraps.Probability.GraphPointLocalTimeApproximation
public import TimeTraps.Probability.SecondMomentGeometricTail
public import TimeTraps.Probability.GraphLocalTimeCanonicalAlmostSure

@[expose] public section

/-! The actual graph occupation approximants converge almost surely,
uniformly on every finite time interval, to one canonical continuous
path functional valid under every initial graph law. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_increment_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H : ℝ≥0) (n : ℕ) :
    Integrable (fun p => ‖graphLocalTimeCompactRestriction H (P.localTimeApproximant a (n + 1) p) -
      graphLocalTimeCompactRestriction H (P.localTimeApproximant a n p)‖ ^ 2) (P.continuousPathLaw hκ x) := by
  simp only [P.localTimeApproximant_compact]
  exact P.occupationCompact_sub_norm_sq_integrable hκ x _ _ H

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_increment_summable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (N : ℕ) :
    (∑' n, P.continuousPathLaw hκ x {p | (1 / 2 : ℝ) ^ n <
      ‖graphLocalTimeCompactRestriction (N : ℝ≥0) (P.localTimeApproximant a (n + 1) p) -
        graphLocalTimeCompactRestriction (N : ℝ≥0) (P.localTimeApproximant a n p)‖}) ≠ ∞ := by
  let inst := P.continuousPathLaw_probability hκ x
  obtain ⟨C, _, hb⟩ := P.localTimeRadius_difference_moment hκ
  apply geometric_secondMoment_exceedance_summable
    (P.localTimeApproximant_increment_integrable hκ x a (N : ℝ≥0))
    (C := 64 * C * ((N : ℝ) + 2 * Real.sqrt (N : ℝ)) + 8)
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [P.localTimeApproximant_compact]
  exact hb (N : ℝ≥0) x a n (by exact_mod_cast Nat.le_succ_of_le hn)

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_hasLimit_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, GraphLocalTimeCanonicalHasLimit (P.localTimeApproximant a) p :=
  graphLocalTimeCanonical_hasLimit_ae (P.localTimeApproximant a) (P.continuousPathLaw hκ x)
    (fun _ n => (1 / 2 : ℝ) ^ n)
    (fun _ => summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (P.localTimeApproximant_increment_summable hκ x a)

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimePath
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) : C(ℝ≥0, ℝ) :=
  graphLocalTimeCanonicalPath (P.localTimeApproximant a) p

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_tendsto_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, Tendsto (fun n => P.localTimeApproximant a n p) atTop
      (𝓝 (P.pointLocalTimePath a p)) :=
  (P.localTimeApproximant_hasLimit_ae hκ x a).mono (fun _ h => h.tendsto)

theorem GraphShiftedContactOperatorProblem.localTimeApproximant_uniform_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ T : ℝ≥0,
      Tendsto (fun n => ⨆ t : Icc (0 : ℝ≥0) T,
        |graphOccupation P.geometry (P.geometry.pointBump a (P.localTimeRadius n)) t.val p -
          P.pointLocalTimePath a p t.val|) atTop (𝓝 0) :=
  (P.localTimeApproximant_hasLimit_ae hκ x a).mono (fun _ h T => h.compact_sup_tendsto T)

end TimeTraps.Analysis
