module

public import TimeTraps.Probability.SampledFourthMomentGrid
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentChainingPath
public import TimeTraps.Probability.BrownianDenseContinuityRecovery

@[expose] public section

/-! Continuous reconstruction from a countable family. Consistency at
repeated time labels is required and retained explicitly. No process at
the uncountably many remaining times is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [CompleteSpace E]
variable {P : Measure Ω} {X : ℕ → Ω → E} {C : ℝ}

omit [MeasurableSpace Ω] in
theorem FourthDyadicRegular.path_eq_coordinate {v : ℕ → E}
    (hv : FourthDyadicRegular v) (i : ℕ) : fourthDyadicPath (brownianDyadicTime i) v = v i := by
  obtain ⟨n, k, rfl⟩ : ∃ n k, Nat.pair n k = i :=
    ⟨(Nat.unpair i).1, (Nat.unpair i).2, Nat.pair_unpair i⟩
  have he (l : ℕ) : fourthDyadicStep (brownianDyadicTime (Nat.pair n k)) (l + n) v =
      v (Nat.pair n k) := by
    rw [Nat.add_comm l n]
    unfold fourthDyadicStep
    rw [brownianDyadicFloor_at_grid]
    exact hv.consistent _ _ (brownianDyadicTime_refine_many n k l)
  apply tendsto_nhds_unique ((hv.tendsto (brownianDyadicTime (Nat.pair n k))).comp
    (tendsto_add_atTop_nat n))
  simpa only [Function.comp_def, he] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => v (Nat.pair n k)) atTop (𝓝 (v (Nat.pair n k))))

omit [CompleteSpace E] in
theorem sampledFourthDyadicRegular_measurableSet (hX : ∀ i, StronglyMeasurable (X i)) :
    MeasurableSet {ω | FourthDyadicRegular (fun i => X i ω)} := by
  have he : {ω | FourthDyadicRegular (fun i => X i ω)} =
      {ω | (∀ i j, brownianDyadicTime i = brownianDyadicTime j → X i ω = X j ω) ∧
        ∀ R : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k < R * 64 ^ n,
          dist (X (Nat.pair n (k + 1)) ω) (X (Nat.pair n k) ω) < (1 / 2 : ℝ) ^ n} := by
    ext ω
    exact ⟨fun h => ⟨h.consistent, h.increments⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [he]
  have hm (i j : ℕ) : Measurable (fun ω => dist (X i ω) (X j ω)) :=
    ((hX i).dist (hX j)).measurable
  have heq (i j : ℕ) : MeasurableSet {ω | X i ω = X j ω} :=
    (hX i).measurableSet_eq_fun (hX j)
  measurability

noncomputable def sampledFourthContinuousVersion (X : ℕ → Ω → E) (t : ℝ≥0) (ω : Ω) : E := by
  classical
  exact if FourthDyadicRegular (fun i => X i ω) then
    fourthDyadicPath t (fun i => X i ω) else 0

omit [MeasurableSpace Ω] in
theorem sampledFourthContinuousVersion_continuous (X : ℕ → Ω → E) (ω : Ω) :
    Continuous (fun t => sampledFourthContinuousVersion X t ω) := by
  by_cases hr : FourthDyadicRegular (fun i => X i ω)
  · simpa only [sampledFourthContinuousVersion, if_pos hr] using hr.continuous
  · simp only [sampledFourthContinuousVersion, if_neg hr]
    exact continuous_const

theorem sampledFourthContinuousVersion_stronglyMeasurable
    (hX : ∀ i, StronglyMeasurable (X i)) (t : ℝ≥0) :
    StronglyMeasurable (sampledFourthContinuousVersion X t) := by
  apply StronglyMeasurable.ite (sampledFourthDyadicRegular_measurableSet hX)
  · apply StronglyMeasurable.limUnder
    intro n
    exact hX _
  · exact stronglyMeasurable_const

theorem sampledFourthContinuousVersion_recovers_ae [IsFiniteMeasure P]
    (hc : ∀ᵐ ω ∂P, ∀ i j, brownianDyadicTime i = brownianDyadicTime j → X i ω = X j ω)
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤
      C * dist (brownianDyadicTime s) (brownianDyadicTime t) ^ 2) :
    ∀ᵐ ω ∂P, ∀ i, sampledFourthContinuousVersion X (brownianDyadicTime i) ω = X i ω := by
  filter_upwards [sampledFourthDyadic_regular_ae hc hi hb] with ω hr
  intro i
  simpa only [sampledFourthContinuousVersion, if_pos hr] using hr.path_eq_coordinate i

end TimeTraps.Probability
