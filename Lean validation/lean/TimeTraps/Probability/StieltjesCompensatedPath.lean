module

public import TimeTraps.Probability.StieltjesWeightedIncrementBound

@[expose] public section

/-! A continuous path with finitely many Stieltjes compensators has a
literal limit of its survival-weighted increments. The contact identity
then cancels those compensators, leaving only the running-cost integral
and the terminal value. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal Topology

variable {I : Type*} [Fintype I]

theorem dyadicWeightedIncrement_compensated_tendsto
    (K B : StieltjesFunction ℝ) (L : I → StieltjesFunction ℝ)
    (q : ℝ≥0 → ℝ) (c : I → ℝ) (hK : Continuous K) (hq : Continuous q) (T : ℝ≥0) :
    Tendsto (dyadicWeightedIncrement (fun t => 1 - K (t : ℝ))
      (fun t => q t + B (t : ℝ) - ∑ i, c i * L i (t : ℝ)) T) atTop
      (𝓝 (((1 - K (T : ℝ)) * q T - (1 - K 0) * q 0) +
        (∫ r in Ioc (0 : ℝ) (T : ℝ), q r.toNNReal ∂K.measure) +
        (∫ r in Ioc (0 : ℝ) (T : ℝ), 1 - K (r.toNNReal : ℝ) ∂B.measure) -
        ∑ i, c i * ∫ r in Ioc (0 : ℝ) (T : ℝ), 1 - K (r.toNNReal : ℝ) ∂(L i).measure)) := by
  have hH : Continuous (fun t : ℝ≥0 => 1 - K (t : ℝ)) :=
    continuous_const.sub (hK.comp NNReal.continuous_coe)
  have hqL := dyadicWeightedIncrement_loss_tendsto K q hq T
  have hbL := dyadicWeightedIncrement_stieltjes_tendsto B (fun t => 1 - K (t : ℝ)) hH T
  have hiL := tendsto_finsetSum Finset.univ (fun i _ =>
    (dyadicWeightedIncrement_stieltjes_tendsto (L i) (fun t => 1 - K (t : ℝ)) hH T).const_mul (c i))
  have he (n : ℕ) : dyadicWeightedIncrement (fun t => 1 - K (t : ℝ))
      (fun t => q t + B (t : ℝ) - ∑ i, c i * L i (t : ℝ)) T n =
      dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) q T n +
        dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) (fun t => B (t : ℝ)) T n -
        ∑ i, c i * dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) (fun t => L i (t : ℝ)) T n := by
    rw [dyadicWeightedIncrement_sub, dyadicWeightedIncrement_add, dyadicWeightedIncrement_sum]
    simp only [dyadicWeightedIncrement_const_mul]
  have h := (hqL.add hbL).sub hiL
  simp only [NNReal.val_eq_coe] at h
  rw [show dyadicWeightedIncrement (fun t => 1 - K (t : ℝ))
      (fun t => q t + B (t : ℝ) - ∑ i, c i * L i (t : ℝ)) T =
      (fun n => dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) q T n +
        dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) (fun t => B (t : ℝ)) T n -
        ∑ i, c i * dyadicWeightedIncrement (fun t => 1 - K (t : ℝ)) (fun t => L i (t : ℝ)) T n)
      from funext he]
  exact h

theorem dyadicWeightedIncrement_contact_cancel_tendsto
    (K B : StieltjesFunction ℝ) (L : I → StieltjesFunction ℝ)
    (q : ℝ≥0 → ℝ) (c : I → ℝ) (hK : Continuous K) (hq : Continuous q) (T : ℝ≥0)
    (hc : (∫ r in Ioc (0 : ℝ) (T : ℝ), q r.toNNReal ∂K.measure) =
      ∑ i, c i * ∫ r in Ioc (0 : ℝ) (T : ℝ), 1 - K (r.toNNReal : ℝ) ∂(L i).measure) :
    Tendsto (dyadicWeightedIncrement (fun t => 1 - K (t : ℝ))
      (fun t => q t + B (t : ℝ) - ∑ i, c i * L i (t : ℝ)) T) atTop
      (𝓝 (((1 - K (T : ℝ)) * q T - (1 - K 0) * q 0) +
        ∫ r in Ioc (0 : ℝ) (T : ℝ), 1 - K (r.toNNReal : ℝ) ∂B.measure)) := by
  have h := dyadicWeightedIncrement_compensated_tendsto K B L q c hK hq T
  rw [hc] at h
  convert h using 1
  congr 1
  ring

end TimeTraps.Probability
