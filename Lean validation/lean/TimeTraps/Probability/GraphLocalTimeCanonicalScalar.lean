module

public import TimeTraps.Probability.GraphLocalTimeCanonicalData

@[expose] public section

/-! A scalar limit uses only the scalar approximating sequence. Its
zero convention is triggered by failure of that sequence to converge,
independently of convergence of any future path observations. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

variable {Ω Ω' : Type*}

def graphLocalTimeScalarLimit (F : ℕ → Ω → ℝ) (ω : Ω) : ℝ := by
  classical
  exact if ∃ l : ℝ, Tendsto (fun n => F n ω) atTop (𝓝 l) then
    limUnder atTop (fun n => F n ω) else 0

theorem graphLocalTimeScalarLimit_eq_of_tendsto (F : ℕ → Ω → ℝ) {ω : Ω} {l : ℝ}
    (h : Tendsto (fun n => F n ω) atTop (𝓝 l)) : graphLocalTimeScalarLimit F ω = l := by
  rw [graphLocalTimeScalarLimit, if_pos ⟨l, h⟩, h.limUnder_eq]

theorem graphLocalTimeScalarLimit_zero_off (F : ℕ → Ω → ℝ) {ω : Ω}
    (h : ¬ ∃ l : ℝ, Tendsto (fun n => F n ω) atTop (𝓝 l)) : graphLocalTimeScalarLimit F ω = 0 :=
  if_neg h

theorem graphLocalTimeScalarLimit_measurable [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n)) : Measurable (graphLocalTimeScalarLimit F) := by
  exact Measurable.ite (StronglyMeasurable.measurableSet_exists_tendsto
    (l := atTop) (fun n => (hF n).stronglyMeasurable))
    (StronglyMeasurable.limUnder (l := atTop) (fun n => (hF n).stronglyMeasurable)).measurable measurable_const

theorem graphLocalTimeScalarLimit_congr (F : ℕ → Ω → ℝ) (G : ℕ → Ω' → ℝ)
    {ω : Ω} {ω' : Ω'} (h : ∀ n, F n ω = G n ω') :
    graphLocalTimeScalarLimit F ω = graphLocalTimeScalarLimit G ω' := by
  classical
  exact congrArg (fun s : ℕ → ℝ => if ∃ l : ℝ, Tendsto s atTop (𝓝 l)
    then limUnder atTop s else 0) (funext h)

end TimeTraps.Probability

end
