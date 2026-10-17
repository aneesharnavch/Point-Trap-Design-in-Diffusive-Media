module

public import TimeTraps.Probability.BrownianPredictableDensitySetGenerators
public import TimeTraps.Probability.BrownianPredictableDensityUnion

@[expose] public section

/-! The pi-lambda argument derives membership for every predictable-set
indicator from actual elementary processes and closedness in L2. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter Function
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable [IsFiniteMeasure P]

theorem brownianPredictableDensityMember_iUnion (T : ℝ≥0) (E : ℕ → Set (ℝ≥0 × Ω))
    (hd : Pairwise (Disjoint on E))
    (hE : ∀ i, MeasurableSet[(brownianNaturalFiltration B hBm).predictable] (E i))
    (hm : ∀ i, BrownianPredictableDensityMember B hBm P (brownianPredictableCutoffIndicator T (E i))) :
    BrownianPredictableDensityMember B hBm P (brownianPredictableCutoffIndicator T (⋃ i, E i)) := by
  let F := brownianNaturalFiltration B hBm
  apply brownianPredictableDensityMember_limit
    (f := fun n => brownianPredictableCutoffIndicator T (⋃ i ∈ Finset.range n, E i))
    (H := brownianPredictableCutoffIndicator T univ)
  · intro n
    rw [brownianPredictableCutoffIndicator_finset_union T E hd]
    exact brownianPredictableDensityMember_sum (Finset.range n) _ (fun i _ => hm i)
  · exact brownianPredictableCutoffIndicator_memLp F T (MeasurableSet.iUnion hE)
  · exact brownianPredictableCutoffIndicator_memLp F T MeasurableSet.univ
  · intro n
    exact Eventually.of_forall (brownianPredictableCutoffIndicator_bound T _)
  · exact Eventually.of_forall (brownianPredictableCutoffIndicator_bound T _)
  · exact Eventually.of_forall (brownianPredictableCutoffIndicator_union_tendsto T E)

theorem brownianPredictableDensityMember_indicator (T : ℝ≥0) (E : Set (ℝ≥0 × Ω))
    (hE : MeasurableSet[(brownianNaturalFiltration B hBm).predictable] E) :
    BrownianPredictableDensityMember B hBm P (brownianPredictableCutoffIndicator T E) := by
  apply MeasurableSpace.induction_on_inter
    (m := (brownianNaturalFiltration B hBm).predictable)
    (C := fun E _ => BrownianPredictableDensityMember B hBm P
      (brownianPredictableCutoffIndicator T E))
    (brownianPredictableGenerators_generate (brownianNaturalFiltration B hBm)).symm
    (brownianPredictableGenerators_isPiSystem (brownianNaturalFiltration B hBm))
    (t := E) (ht := hE)
  · rw [brownianPredictableCutoffIndicator_empty]
    exact brownianPredictableDensityMember_zero
  · exact brownianPredictableDensityMember_generator T
  · intro E _ hm
    exact brownianPredictableDensityMember_compl T E hm
  · intro E hd hE hm
    exact brownianPredictableDensityMember_iUnion T E hd hE hm

theorem brownianPredictableDensity_indicator_mem_integralSpace (T : ℝ≥0)
    (E : Set (ℝ≥0 × Ω))
    (hE : MeasurableSet[(brownianNaturalFiltration B hBm).predictable] E)
    (hL : MemLp (brownianPredictableCutoffIndicator T E) 2 (volume.prod P)) :
    hL.toLp (brownianPredictableCutoffIndicator T E) ∈ brownianIntegralSpace B hBm P :=
  brownianPredictableDensityMember_toLp (brownianPredictableDensityMember_indicator T E hE) hL

end TimeTraps.Probability
