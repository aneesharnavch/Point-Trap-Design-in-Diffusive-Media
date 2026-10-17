module

public import TimeTraps.Probability.BrownianConstruction
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

/-! Joint measurability of the exact constructed process, including on the
exceptional samples. The proof uses its measurable grid-limit definition,
not an inference from almost-sure path continuity. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianDyadicFloor_measurable (n : ℕ) : Measurable (fun t => brownianDyadicFloor t n) := by
  apply Measurable.nat_floor
  exact (by fun_prop : Measurable (fun t : ℝ≥0 => t.val * (64 : ℝ) ^ n))

theorem brownianDyadicStep_jointly_measurable (n : ℕ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianDyadicStep p.1 n p.2) := by
  have he : Measurable (fun p : (ℕ → ℝ) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply k)
  have hi : Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => Nat.pair n (brownianDyadicFloor p.1 n)) :=
    (measurable_of_countable (Nat.pair n)).comp ((brownianDyadicFloor_measurable n).comp measurable_fst)
  exact he.comp (measurable_snd.prodMk hi)

theorem brownianDyadicPath_jointly_measurable :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianDyadicPath p.1 p.2) := by
  apply StronglyMeasurable.measurable
  exact StronglyMeasurable.limUnder
    (fun n => (brownianDyadicStep_jointly_measurable n).stronglyMeasurable)

end TimeTraps.Probability
