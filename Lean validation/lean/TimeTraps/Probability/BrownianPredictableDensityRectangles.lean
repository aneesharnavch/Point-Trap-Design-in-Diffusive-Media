module

public import TimeTraps.Probability.BrownianIntegralClosure
public import TimeTraps.Probability.BrownianIntegralPredictable

@[expose] public section

/-! The finite predictable rectangles are actual members of the already
constructed elementary integral space. This is the generator step for
predictable L2 density, and does not assume density itself. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)}
variable {P : Measure Ω} [IsFiniteMeasure P]

noncomputable def brownianPredictableRectangleElementary
    (s t : ℝ≥0) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[brownianNaturalFiltration B hBm s] A) (c : ℝ) :
    BrownianIntegralElementary B hBm P where
  left := s
  right := t
  ordered := hst
  coefficient := A.indicator (fun _ => c)
  adapted := (measurable_const.indicator hA).stronglyMeasurable
  squareIntegrable := (memLp_const c).indicator ((brownianNaturalFiltration B hBm).le s _ hA)

theorem brownianPredictableRectangle_process (s t : ℝ≥0) (A : Set Ω) (c : ℝ) :
    brownianElementaryProcess s t (A.indicator (fun _ => c)) =
      (Ioc s.val t.val ×ˢ A).indicator (fun _ : ℝ × Ω => c) := by
  funext p
  rcases p with ⟨r, ω⟩
  unfold brownianElementaryProcess brownianIntervalIndicator
  by_cases ht : r ∈ Ioc s.val t.val
  · by_cases hω : ω ∈ A
    · rw [indicator_of_mem ht, indicator_of_mem hω, indicator_of_mem (show (r, ω) ∈
        Ioc s.val t.val ×ˢ A from ⟨ht, hω⟩), one_mul]
    · rw [indicator_of_mem ht, indicator_of_notMem hω,
        indicator_of_notMem (show (r, ω) ∉ Ioc s.val t.val ×ˢ A from fun h => hω h.2), mul_zero]
  · rw [indicator_of_notMem ht,
      indicator_of_notMem (show (r, ω) ∉ Ioc s.val t.val ×ˢ A from fun h => ht h.1), zero_mul]

theorem brownianPredictableRectangle_memLp (s t : ℝ≥0) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[brownianNaturalFiltration B hBm s] A) (c : ℝ) :
    MemLp ((Ioc s.val t.val ×ˢ A).indicator (fun _ : ℝ × Ω => c)) 2 (volume.prod P) := by
  have hi := (brownianPredictableRectangleElementary (P := P) s t hst A hA c).process_memLp
  change MemLp (brownianElementaryProcess s t (A.indicator (fun _ => c))) 2 (volume.prod P) at hi
  rw [brownianPredictableRectangle_process] at hi
  exact hi

theorem brownianPredictableRectangle_mem_integralSpace (s t : ℝ≥0) (hst : s ≤ t) (A : Set Ω)
    (hA : MeasurableSet[brownianNaturalFiltration B hBm s] A) (c : ℝ)
    (hf : MemLp ((Ioc s.val t.val ×ˢ A).indicator (fun _ : ℝ × Ω => c)) 2 (volume.prod P)) :
    hf.toLp ((Ioc s.val t.val ×ˢ A).indicator (fun _ : ℝ × Ω => c)) ∈
      brownianIntegralSpace B hBm P := by
  let a := brownianPredictableRectangleElementary (P := P) s t hst A hA c
  have he : hf.toLp ((Ioc s.val t.val ×ˢ A).indicator (fun _ : ℝ × Ω => c)) = a.processL2 := by
    apply Lp.ext
    filter_upwards [hf.coeFn_toLp, a.processL2_coe] with p hp hq
    rw [hp, hq]
    exact (congrFun (brownianPredictableRectangle_process s t A c) p).symm
  rw [he]
  exact (brownianIntegralGenerator a).property

end TimeTraps.Probability
