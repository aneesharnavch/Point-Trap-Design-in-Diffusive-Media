module

public import TimeTraps.Probability.GraphPointOccupationL2
public import Mathlib.Topology.Sequences

@[expose] public section

/-! The graph point-local-time L2 limit is independent of the shrinking
positive radii. Interleaving two approximations proves uniqueness without
postulating a limit-identification principle for occupations. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Probability TimeTraps.Graph
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_tendsto_sequence
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => P.occupationL2 hκ x (P.geometry.pointBump a (r n)) T)
      atTop (𝓝 (P.pointLocalTimeL2 hκ x a T)) := by
  let s : ℕ → ℝ := fun n => if n % 2 = 0 then 1 / ((n : ℝ) + 1) else r n
  have hs : ∀ n, 0 < s n := by
    intro n
    dsimp only [s]
    split_ifs
    · positivity
    · exact hr n
  have hs0 : Tendsto s atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.if' hr0
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun n => by omega)).tendsto_atTop
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun n => by omega)).tendsto_atTop
  have he : Tendsto ((fun n => P.occupationL2 hκ x (P.geometry.pointBump a (s n)) T) ∘
      (fun n => 2 * n)) atTop (𝓝 (P.pointLocalTimeL2 hκ x a T)) := by
    simpa [Function.comp_def, s] using (P.pointLocalTimeL2_tendsto hκ x a T).comp heven
  have hall := tendsto_nhds_of_cauchySeq_of_subseq
    (P.pointOccupationL2_cauchy hκ x a T hs hs0) heven he
  apply tendsto_nhds_of_cauchySeq_of_subseq
    (P.pointOccupationL2_cauchy hκ x a T hr hr0) hodd
  simpa [Function.comp_def, s, Nat.add_mod] using hall.comp hodd

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_tendsto_radius
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    Tendsto (fun r : ℝ => P.occupationL2 hκ x (P.geometry.pointBump a r) T)
      (𝓝[>] 0) (𝓝 (P.pointLocalTimeL2 hκ x a T)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro r hr
  have hr0 : Tendsto r atTop (𝓝 0) := hr.mono_right inf_le_left
  have hrp : ∀ᶠ n in atTop, 0 < r n := hr.eventually self_mem_nhdsWithin
  let s : ℕ → ℝ := fun n => if 0 < r n then r n else 1 / ((n : ℝ) + 1)
  have hs : ∀ n, 0 < s n := by
    intro n
    dsimp only [s]
    split_ifs with h
    · exact h
    · positivity
  have hs0 : Tendsto s atTop (𝓝 0) := hr0.if' tendsto_one_div_add_atTop_nhds_zero_nat
  apply (P.pointLocalTimeL2_tendsto_sequence hκ x a T hs hs0).congr'
  filter_upwards [hrp] with n hn
  simp only [s, if_pos hn, Function.comp_apply]

end TimeTraps.Analysis
