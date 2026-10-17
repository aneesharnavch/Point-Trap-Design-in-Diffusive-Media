module

public import TimeTraps.Probability.BrownianPredictableDensitySimple
public import TimeTraps.Probability.BrownianPredictableDensityApproximation
public import Mathlib.Topology.Sequences

@[expose] public section

/-! Full predictable L2 density on a finite horizon. Every predictable
scalar process whose cutoff is square integrable belongs to the existing
closed span of adapted elementary integrands. No path continuity or
boundedness of the process is assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable [IsFiniteMeasure P]

theorem brownianPredictableDensityMember_process (H : ℝ≥0 → Ω → ℝ)
    (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H) (T : ℝ≥0)
    (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    BrownianPredictableDensityMember B hBm P (brownianSquareProcess H T) := by
  apply brownianPredictableDensityMember_limit
    (f := fun n => brownianSquareProcess
      (fun t ω => brownianPredictableSimpleApprox hH n (t, ω)) T)
    (H := fun p => 2 * |brownianSquareProcess H T p|)
  · intro n
    exact brownianPredictableDensityMember_simple T (brownianPredictableSimpleApprox hH n)
  · exact hL
  · simpa only [Real.norm_eq_abs] using hL.norm.const_mul (2 : ℝ)
  · intro n
    exact Eventually.of_forall (brownianPredictableSimpleApprox_cutoff_bound hH T n)
  · exact Eventually.of_forall (fun p => by nlinarith [abs_nonneg (brownianSquareProcess H T p)])
  · exact Eventually.of_forall (brownianPredictableSimpleApprox_cutoff_tendsto hH T)

theorem brownianPredictableDensity_process_mem_integralSpace (H : ℝ≥0 → Ω → ℝ)
    (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H) (T : ℝ≥0)
    (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    hL.toLp (brownianSquareProcess H T) ∈ brownianIntegralSpace B hBm P :=
  brownianPredictableDensityMember_toLp (brownianPredictableDensityMember_process H hH T hL) hL

theorem brownianPredictableDensity_elementary_approximation (H : ℝ≥0 → Ω → ℝ)
    (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H) (T : ℝ≥0)
    (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    ∃ f : ℕ → Lp ℝ 2 (volume.prod P),
      (∀ n, f n ∈ brownianIntegralStepSpace B hBm P) ∧
      Tendsto f atTop (𝓝 (hL.toLp (brownianSquareProcess H T))) := by
  have hm := brownianPredictableDensity_process_mem_integralSpace H hH T hL
  change hL.toLp (brownianSquareProcess H T) ∈
    closure (brownianIntegralStepSpace B hBm P : Set (Lp ℝ 2 (volume.prod P))) at hm
  exact mem_closure_iff_seq_limit.mp hm

noncomputable def brownianPredictableIntegrand (H : ℝ≥0 → Ω → ℝ)
    (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H) (T : ℝ≥0)
    (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    brownianIntegralSpace B hBm P :=
  ⟨hL.toLp (brownianSquareProcess H T),
    brownianPredictableDensity_process_mem_integralSpace H hH T hL⟩

theorem brownianPredictableIntegrand_coe (H : ℝ≥0 → Ω → ℝ)
    (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H) (T : ℝ≥0)
    (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    (brownianPredictableIntegrand H hH T hL : Lp ℝ 2 (volume.prod P)) =ᵐ[volume.prod P]
      brownianSquareProcess H T := hL.coeFn_toLp

end TimeTraps.Probability
