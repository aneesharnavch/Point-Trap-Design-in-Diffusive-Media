module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentKolmogorovGrid
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentChainingPath

@[expose] public section

/-! A measurable continuous modification derived from fourth-moment
increments. Almost-sure dyadic convergence and convergence in measure
identify it with the original process at each fixed parameter. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [CompleteSpace E]
variable {P : Measure Ω} {X : ℝ≥0 → Ω → E} {C : ℝ}

omit [CompleteSpace E] in
theorem fourthDyadicRegular_measurableSet (hX : ∀ t, StronglyMeasurable (X t)) :
    MeasurableSet {ω | FourthDyadicRegular (fun i => X (brownianDyadicTime i) ω)} := by
  have he : {ω | FourthDyadicRegular (fun i => X (brownianDyadicTime i) ω)} =
      {ω | ∀ R : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k < R * 64 ^ n,
        dist (X (brownianDyadicTime (Nat.pair n (k + 1))) ω)
          (X (brownianDyadicTime (Nat.pair n k)) ω) < (1 / 2 : ℝ) ^ n} := by
    ext ω
    exact ⟨fun h => h.increments, fun h => ⟨fun i j hij => congrArg (fun t => X t ω) hij, h⟩⟩
  rw [he]
  have hm (s t : ℝ≥0) : Measurable (fun ω => dist (X s ω) (X t ω)) :=
    ((hX s).dist (hX t)).measurable
  measurability

noncomputable def fourthContinuousVersion (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E := by
  classical
  exact if FourthDyadicRegular (fun i => X (brownianDyadicTime i) ω) then
    fourthDyadicPath t (fun i => X (brownianDyadicTime i) ω) else 0

omit [MeasurableSpace Ω] in
theorem fourthContinuousVersion_continuous (X : ℝ≥0 → Ω → E) (ω : Ω) :
    Continuous (fun t => fourthContinuousVersion X t ω) := by
  by_cases hr : FourthDyadicRegular (fun i => X (brownianDyadicTime i) ω)
  · simpa only [fourthContinuousVersion, if_pos hr] using hr.continuous
  · simp only [fourthContinuousVersion, if_neg hr]
    exact continuous_const

theorem fourthContinuousVersion_stronglyMeasurable (hX : ∀ t, StronglyMeasurable (X t)) (t : ℝ≥0) :
    StronglyMeasurable (fourthContinuousVersion X t) := by
  apply StronglyMeasurable.ite (fourthDyadicRegular_measurableSet hX)
  · apply StronglyMeasurable.limUnder
    intro n
    exact hX _
  · exact stronglyMeasurable_const

theorem fourthContinuousVersion_ae_eq [IsFiniteMeasure P]
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist s t ^ 2) (t : ℝ≥0) :
    fourthContinuousVersion X t =ᵐ[P] X t := by
  have ht : Tendsto (fun n => brownianDyadicTime (Nat.pair n (brownianDyadicFloor t n))) atTop (𝓝 t) :=
    NNReal.tendsto_coe.mp (brownianDyadicTime_floor_tendsto t)
  obtain ⟨u, hu, hlim⟩ := (fourthMoment_tendstoInMeasure hi hb ht).exists_seq_tendsto_ae
  filter_upwards [fourthDyadic_regular_ae hi hb, hlim] with ω hr hω
  simp only [fourthContinuousVersion, if_pos hr]
  exact tendsto_nhds_unique ((hr.tendsto t).comp hu.tendsto_atTop) hω

end TimeTraps.Probability
