module

public import TimeTraps.Probability.BrownianLocalTimeSupportFixed
public import TimeTraps.Probability.BrownianLocalTimeGlobal

@[expose] public section

/-! A measurable away-from-level event is specified by countably many
dense time probes together with the proved Brownian regularity event.
Continuity extends the probe inequalities to the whole closed interval. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped NNReal Topology

def brownianLocalTimeAwayProbe (S T : ℝ≥0) (hST : S ≤ T) : ℕ → Icc S T := by
  letI : Nonempty (Icc S T) := ⟨⟨S, le_rfl, hST⟩⟩
  exact denseSeq (Icc S T)

theorem brownianLocalTimeAwayProbe_denseRange (S T : ℝ≥0) (hST : S ≤ T) :
    DenseRange (brownianLocalTimeAwayProbe S T hST) := by
  let : Nonempty (Icc S T) := ⟨⟨S, le_rfl, hST⟩⟩
  exact denseRange_denseSeq (Icc S T)

def brownianLocalTimeAwayEvent (a δ : ℝ) (S T : ℝ≥0) (hST : S ≤ T)
    (ω : ℕ → ℝ) : Prop :=
  BrownianDyadicRegular ω ∧ ∀ k,
    δ ≤ |brownianDyadicPath (brownianLocalTimeAwayProbe S T hST k).val ω - a|

theorem brownianLocalTimeAwayEvent_measurableSet (a δ : ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    MeasurableSet {ω | brownianLocalTimeAwayEvent a δ S T hST ω} := by
  apply brownianDyadicRegular_measurableSet.inter
  change MeasurableSet {ω | ∀ k,
    δ ≤ |brownianDyadicPath (brownianLocalTimeAwayProbe S T hST k).val ω - a|}
  rw [ofPred_forall]
  exact MeasurableSet.iInter (fun k => measurableSet_le measurable_const
    ((brownianDyadicPath_measurable _).sub_const a).abs)

theorem brownianLocalTimeAwayProbe_bound {a δ : ℝ} {S T : ℝ≥0} {hST : S ≤ T}
    {f : ℝ≥0 → ℝ} (hf : Continuous f)
    (hp : ∀ k, δ ≤ |f (brownianLocalTimeAwayProbe S T hST k).val - a|) :
    ∀ s ∈ Icc S T, δ ≤ |f s - a| := by
  have hc : IsClosed {s : Icc S T | δ ≤ |f s.val - a|} :=
    isClosed_le continuous_const
      ((hf.comp continuous_subtype_val).sub continuous_const).abs
  have hs : Set.range (brownianLocalTimeAwayProbe S T hST) ⊆
      {s : Icc S T | δ ≤ |f s.val - a|} := by
    rintro s ⟨k, rfl⟩
    exact hp k
  intro s hst
  exact (closure_minimal hs hc) ((brownianLocalTimeAwayProbe_denseRange S T hST) ⟨s, hst⟩)

theorem brownianLocalTimeAwayEvent_away {a δ : ℝ} {S T : ℝ≥0} {hST : S ≤ T}
    {ω : ℕ → ℝ} (hω : brownianLocalTimeAwayEvent a δ S T hST ω) :
    ∀ s ∈ Icc S T, δ ≤ |brownianDyadicPath s ω - a| :=
  brownianLocalTimeAwayProbe_bound (BrownianDyadicRegular.continuous hω.1) hω.2

theorem brownianLocalTimeGlobalPath_eq_on_away_event (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {S T : ℝ≥0} (hST : S ≤ T) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianLocalTimeAwayEvent a δ S T hST ω →
      brownianLocalTimeGlobalPath a T ω = brownianLocalTimeGlobalPath a S ω := by
  have he := brownianTanakaCompensation_eq_on_away_event
    brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a hST hδ
    {ω | brownianLocalTimeAwayEvent a δ S T hST ω}
    (fun _ hω => brownianLocalTimeAwayEvent_away hω)
  filter_upwards [he, brownianLocalTimeGlobalPath_compensation_ae a T,
    brownianLocalTimeGlobalPath_compensation_ae a S] with ω heq ht hs
  intro hω
  exact ht.trans ((heq hω).trans hs.symm)

end TimeTraps.Probability

end
