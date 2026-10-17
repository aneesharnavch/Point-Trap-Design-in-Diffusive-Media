module

public import TimeTraps.Analysis.PositiveTimeChangeInverse

@[expose] public section

/-! Continuous dependence of inverse positive clocks on arbitrary
parameters. Continuity of each fixed-time clock is enough: the order
isomorphism identities turn both inverse sublevel tests into open sets. -/

namespace TimeTraps.Analysis

open Set
open scoped NNReal

theorem positiveTimeSpeed_family_inverse_continuous
    {P : Type*} [TopologicalSpace P] (v : P → PositiveTimeSpeed)
    (hc : ∀ s, Continuous (fun p => (v p).clock s)) :
    Continuous (fun q : ℝ≥0 × P => (v q.2).inverse q.1) := by
  apply OrderTopology.continuous_iff.mpr
  intro s
  have hl : (fun q : ℝ≥0 × P => (v q.2).inverse q.1) ⁻¹' Ioi s =
      {q | (v q.2).clock s < q.1} := by
    ext q
    change s < (v q.2).inverse q.1 ↔ (v q.2).clock s < q.1
    simpa only [PositiveTimeSpeed.clock_inverse] using
      ((v q.2).clock_strictMono.lt_iff_lt (a := s) (b := (v q.2).inverse q.1)).symm
  have hr : (fun q : ℝ≥0 × P => (v q.2).inverse q.1) ⁻¹' Iio s =
      {q | q.1 < (v q.2).clock s} := by
    ext q
    change (v q.2).inverse q.1 < s ↔ q.1 < (v q.2).clock s
    simpa only [PositiveTimeSpeed.clock_inverse] using
      ((v q.2).clock_strictMono.lt_iff_lt (a := (v q.2).inverse q.1) (b := s)).symm
  rw [hl, hr]
  exact ⟨isOpen_lt ((hc s).comp continuous_snd) continuous_fst,
    isOpen_lt continuous_fst ((hc s).comp continuous_snd)⟩

end TimeTraps.Analysis
