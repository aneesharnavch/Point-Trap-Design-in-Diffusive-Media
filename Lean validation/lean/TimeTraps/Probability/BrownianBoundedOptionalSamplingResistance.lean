module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingResistanceData

@[expose] public section

/-! The constructed reversible resistance diffusion satisfies the
Neumann martingale problem in the original physical interval. Its
compensator uses F''(R x)/(a(x) rho(x)), proved to be (a u')'/rho
for u=F∘R, with no derivative assumption on a or rho. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

noncomputable def reversibleResistanceFiltration (A : IntervalMedium) (x : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace BrownianCompletedSample) :=
  brownianInverseClockFiltration A.resistanceLength A.resistanceLength_pos 1
    (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y)

noncomputable def reversibleResistanceNeumannDynkin (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) (x : ℝ) (t : ℝ≥0)
    (ω : BrownianCompletedSample) : ℝ :=
  reversibleResistanceNeumannTest A F (reversibleResistancePath A x t ω) -
    reversibleResistanceNeumannTest A F x -
      ∫ r in (0 : ℝ)..t.val,
        reversibleResistanceNeumannGenerator A F (reversibleResistancePath A x r.toNNReal ω)

theorem reversibleResistanceNeumannGenerator_path (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) (x : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistanceNeumannGenerator A F (reversibleResistancePath A x t ω) =
      F.curvature (reversibleResistanceReference A x (reversibleResistanceInversePath A x t ω) ω) /
        A.resistanceSpeed (reversibleResistanceReference A x (reversibleResistanceInversePath A x t ω) ω) := by
  unfold reversibleResistanceNeumannGenerator
  rw [reversibleResistancePath_coordinate]
  rfl

theorem reversibleResistanceNeumannDynkin_eq (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right)
    (t : ℝ≥0) (ω : BrownianCompletedSample) :
    reversibleResistanceNeumannDynkin A F x t ω =
      reflectedTimeChangedNeumannDynkin F 1 (A.resistance x) A.resistanceSpeed t ω := by
  have hvalue : reversibleResistanceNeumannTest A F (reversibleResistancePath A x t ω) =
      F.value (reversibleResistanceReference A x (reversibleResistanceInversePath A x t ω) ω) :=
    congrArg F.value (reversibleResistancePath_coordinate A x t ω)
  have hi : (∫ r in (0 : ℝ)..t.val,
      reversibleResistanceNeumannGenerator A F (reversibleResistancePath A x r.toNNReal ω)) =
      ∫ r in (0 : ℝ)..t.val,
        F.curvature (reversibleResistanceReference A x (reversibleResistanceInversePath A x r.toNNReal ω) ω) /
          A.resistanceSpeed (reversibleResistanceReference A x (reversibleResistanceInversePath A x r.toNNReal ω) ω) := by
    apply intervalIntegral.integral_congr
    intro r _hr
    exact reversibleResistanceNeumannGenerator_path A F x r.toNNReal ω
  have hstart : reflectedFold A.resistanceLength (A.resistance x) = A.resistance x :=
    reflectedFold_eq_self A.resistanceLength A.resistanceLength_pos (A.resistance x) (A.resistance_mem hx)
  unfold reversibleResistanceNeumannDynkin reflectedTimeChangedNeumannDynkin
  rw [hvalue, hi, hstart, one_mul]
  rfl

theorem reversibleResistanceNeumannDynkin_integrable_mean (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right)
    (t : ℝ≥0) : Integrable (reversibleResistanceNeumannDynkin A F x t) brownianCompletedMeasure ∧
      (∫ ω, reversibleResistanceNeumannDynkin A F x t ω ∂brownianCompletedMeasure) = 0 := by
  have he := funext (fun ω => reversibleResistanceNeumannDynkin_eq A F hx t ω)
  rw [he]
  exact reflectedTimeChangedNeumannDynkin_integrable_mean F A.resistanceLength_pos 1
    zero_lt_one (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) t

theorem reversibleResistanceNeumannDynkin_martingale (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right) :
    Martingale (reversibleResistanceNeumannDynkin A F x)
      (reversibleResistanceFiltration A x) brownianCompletedMeasure := by
  have he := funext (fun t => funext (fun ω => reversibleResistanceNeumannDynkin_eq A F hx t ω))
  rw [he]
  exact reflectedTimeChangedNeumannDynkin_martingale F A.resistanceLength_pos 1 zero_lt_one
    (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y)

theorem reversibleResistanceNeumannDynkin_condExp (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianCompletedMeasure[reversibleResistanceNeumannDynkin A F x t | reversibleResistanceFiltration A x s]
      =ᵐ[brownianCompletedMeasure] reversibleResistanceNeumannDynkin A F x s :=
  (reversibleResistanceNeumannDynkin_martingale A F hx).2 s t hst

theorem reversibleResistanceNeumannDynkin_original_aemeasurable (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right)
    (t : ℝ≥0) :
    AEMeasurable (fun ω : ℕ → ℝ => reversibleResistanceNeumannDynkin A F x t ω) brownianDyadicMeasure := by
  have hm := ((reversibleResistanceNeumannDynkin_martingale A F hx).stronglyAdapted t).mono
    ((reversibleResistanceFiltration A x).le t)
  have hn : NullMeasurable (fun ω : ℕ → ℝ => reversibleResistanceNeumannDynkin A F x t ω)
      brownianDyadicMeasure := hm.measurable
  exact hn.aemeasurable

theorem reversibleResistanceNeumannDynkin_original_integrable_mean (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right)
    (t : ℝ≥0) :
    Integrable (fun ω : ℕ → ℝ => reversibleResistanceNeumannDynkin A F x t ω) brownianDyadicMeasure ∧
      (∫ ω : ℕ → ℝ, reversibleResistanceNeumannDynkin A F x t ω ∂brownianDyadicMeasure) = 0 := by
  have ha := (reversibleResistanceNeumannDynkin_original_aemeasurable A F hx t).aestronglyMeasurable
  obtain ⟨hi, hz⟩ := reversibleResistanceNeumannDynkin_integrable_mean A F hx t
  exact ⟨((completedMeasure_identity_preserving brownianDyadicMeasure).integrable_comp ha).mp hi,
    (completedMeasure_integral brownianDyadicMeasure ha).symm.trans hz⟩

end TimeTraps.Probability
