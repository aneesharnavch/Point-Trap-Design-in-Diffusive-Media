module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeRegularity

@[expose] public section

/-! The sum of the two shifted regulator Stieltjes functions is an actual
atomless time measure. On the fixed-level regular event it has the increments
of the periodized correction and is supported where the folded path equals
that level. The statement includes both endpoints and makes no occupation
formula or folded Tanaka assertion. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedFold_eq_of_sub_zero {L z a : ℝ} (hL : 0 < L)
    (ha : a ∈ Icc 0 L) (hz : reflectedFold L (z - a) = 0) :
    reflectedFold L z = a := by
  rcases (reflectedFold_eq_iff_lattice L hL (z - a) 0 ⟨le_rfl, hL.le⟩).mp hz with
    ⟨k, hk | hk⟩
  · exact (reflectedFold_eq_iff_lattice L hL z a ha).mpr ⟨k, Or.inl (by linarith)⟩
  · exact (reflectedFold_eq_iff_lattice L hL z a ha).mpr ⟨k, Or.inl (by linarith)⟩

theorem reflectedFold_eq_of_add_zero {L z a : ℝ} (hL : 0 < L)
    (ha : a ∈ Icc 0 L) (hz : reflectedFold L (z + a) = 0) :
    reflectedFold L z = a := by
  rcases (reflectedFold_eq_iff_lattice L hL (z + a) 0 ⟨le_rfl, hL.le⟩).mp hz with
    ⟨k, hk | hk⟩
  · exact (reflectedFold_eq_iff_lattice L hL z a ha).mpr ⟨k, Or.inr (by linarith)⟩
  · exact (reflectedFold_eq_iff_lattice L hL z a ha).mpr ⟨k, Or.inr (by linarith)⟩

def reflectedInteriorStieltjes (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) : StieltjesFunction ℝ :=
  affineBrownianRegulatorStieltjes (x - a) hσ hL 0 ω +
    affineBrownianRegulatorStieltjes (x + a) hσ hL 0 ω

def reflectedInteriorTimeMeasure (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) : Measure ℝ :=
  (reflectedInteriorStieltjes x hσ hL a ω).measure

theorem reflectedInteriorStieltjes_apply {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (t : ℝ) :
    reflectedInteriorStieltjes x hσ hL a ω t =
      reflectedInteriorCorrection x σ L a t.toNNReal ω := by
  exact congrArg₂ (fun u v : ℝ => u + v)
    (affineBrownianRegulatorStieltjes_apply hσ hL hω.1 0 t)
    (affineBrownianRegulatorStieltjes_apply hσ hL hω.2 0 t)

theorem reflectedInteriorTimeMeasure_eq_add (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) :
    reflectedInteriorTimeMeasure x hσ hL a ω =
      affineBrownianRegulatorTimeMeasure (x - a) hσ hL 0 ω +
      affineBrownianRegulatorTimeMeasure (x + a) hσ hL 0 ω :=
  StieltjesFunction.measure_add _ _

theorem reflectedInteriorTimeMeasure_Ioc {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (S T : ℝ) :
    reflectedInteriorTimeMeasure x hσ hL a ω (Ioc S T) =
      ENNReal.ofReal (reflectedInteriorCorrection x σ L a T.toNNReal ω -
        reflectedInteriorCorrection x σ L a S.toNNReal ω) := by
  calc
    _ = ENNReal.ofReal (reflectedInteriorStieltjes x hσ hL a ω T -
        reflectedInteriorStieltjes x hσ hL a ω S) := StieltjesFunction.measure_Ioc _ _ _
    _ = _ := congrArg ENNReal.ofReal (congrArg₂ (fun u v : ℝ => u - v)
      (reflectedInteriorStieltjes_apply hσ hL hω T)
      (reflectedInteriorStieltjes_apply hσ hL hω S))

theorem reflectedInteriorTimeMeasure_singleton (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) (t : ℝ) :
    reflectedInteriorTimeMeasure x hσ hL a ω {t} = 0 := by
  rw [reflectedInteriorTimeMeasure_eq_add, Measure.add_apply,
    affineBrownianRegulatorTimeMeasure_singleton (x - a) hσ hL 0 ω t,
    affineBrownianRegulatorTimeMeasure_singleton (x + a) hσ hL 0 ω t, add_zero]

theorem reflectedInteriorTimeMeasure_support {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (ha : a ∈ Icc 0 L)
    (hω : reflectedInteriorLocalTimeRegular x σ L a ω) :
    (reflectedInteriorTimeMeasure x hσ hL a ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ reflectedFold L (affineBrownianInput x σ t.toNNReal ω) = a} := by
  rw [reflectedInteriorTimeMeasure_eq_add, Measure.support_add]
  intro t ht
  rcases ht with ht | ht
  · obtain ⟨ht0, he⟩ := (affineBrownianRegulatorTimeMeasure_boundary_support hσ hL hω.1).1 ht
    have hi : affineBrownianInput (x - a) σ t.toNNReal ω =
        affineBrownianInput x σ t.toNNReal ω - a := by
      unfold affineBrownianInput
      ring
    have hz : reflectedFold L (affineBrownianInput x σ t.toNNReal ω - a) = 0 :=
      (congrArg (reflectedFold L) hi).symm.trans he
    exact ⟨ht0, reflectedFold_eq_of_sub_zero hL ha hz⟩
  · obtain ⟨ht0, he⟩ := (affineBrownianRegulatorTimeMeasure_boundary_support hσ hL hω.2).1 ht
    have hi : affineBrownianInput (x + a) σ t.toNNReal ω =
        affineBrownianInput x σ t.toNNReal ω + a := by
      unfold affineBrownianInput
      ring
    have hz : reflectedFold L (affineBrownianInput x σ t.toNNReal ω + a) = 0 :=
      (congrArg (reflectedFold L) hi).symm.trans he
    exact ⟨ht0, reflectedFold_eq_of_add_zero hL ha hz⟩

theorem reflectedInteriorTimeMeasure_support_ae (x : ℝ) {σ L a : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (ha : a ∈ Icc 0 L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, (reflectedInteriorTimeMeasure x hσ hL a ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ reflectedFold L (affineBrownianInput x σ t.toNNReal ω) = a} := by
  filter_upwards [reflectedInteriorLocalTimeRegular_ae x σ L a] with ω hω
  exact reflectedInteriorTimeMeasure_support hσ hL ha hω

end TimeTraps.Probability

end
