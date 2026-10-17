module

public import TimeTraps.Probability.BrownianIntegralRepresentation

@[expose] public section

/-! The completed integral agrees with every finite left-adapted partition
sum. Product-measure almost-everywhere equality of step processes makes the
stochastic sum independent of the chosen partition representation. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def BrownianIntegralElementary.ofPartition {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) (i : Fin N) : BrownianIntegralElementary B hBm P where
  left := τ i.castSucc
  right := τ i.succ
  ordered := hτ (Fin.castSucc_le_succ i)
  coefficient := ξ i
  adapted := hξ i
  squareIntegrable := hξ2 i

def brownianStepProcess {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ)
    (p : ℝ × Ω) : ℝ :=
  ∑ i, brownianElementaryProcess (τ i.castSucc) (τ i.succ) (ξ i) p

def brownianStepIntegrand {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) : brownianIntegralSpace B hBm P :=
  brownianElementarySumIntegrand (BrownianIntegralElementary.ofPartition (B := B) (hBm := hBm) (P := P) τ hτ ξ hξ hξ2)

theorem brownianStepProcess_predictable {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) :
    IsStronglyPredictable (brownianNaturalFiltration B hBm)
      (fun r ω => brownianStepProcess τ ξ (r.val, ω)) :=
  brownianElementarySum_predictable (BrownianIntegralElementary.ofPartition (B := B) (hBm := hBm) (P := P) τ hτ ξ hξ hξ2)

theorem brownianStepProcess_memLp {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) : MemLp (brownianStepProcess τ ξ) 2 (volume.prod P) :=
  memLp_finsetSum _ (fun i _ =>
    (BrownianIntegralElementary.ofPartition (B := B) (hBm := hBm) (P := P)
      τ hτ ξ hξ hξ2 i).process_memLp)

theorem brownianIntegral_step_ae (hB : IsPreBrownianReal B P) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) :
    brownianIntegral hB (@brownianStepIntegrand Ω mΩ B hBm P N τ hτ ξ hξ hξ2) =ᵐ[P]
      brownianStepIntegral B τ ξ :=
  brownianIntegral_elementarySum_ae hB (BrownianIntegralElementary.ofPartition (B := B) (hBm := hBm) (P := P) τ hτ ξ hξ hξ2)

theorem brownianElementarySum_isometry (hB : IsPreBrownianReal B P)
    {I : Type*} [Fintype I] (a : I → BrownianIntegralElementary B hBm P) :
    (∫ p, brownianElementarySum a p ^ 2 ∂volume.prod P) =
      ∫ ω, (∑ i, (a i).coefficient ω * (B (a i).right ω - B (a i).left ω)) ^ 2 ∂P := by
  calc
    _ = ∫ p, (brownianElementarySumIntegrand a :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2 ∂volume.prod P :=
      integral_congr_ae (by
        filter_upwards [brownianElementarySumIntegrand_coe a] with p hp
        rw [hp])
    _ = ∫ ω, (brownianIntegral hB (brownianElementarySumIntegrand a)) ω ^ 2 ∂P :=
      (brownianIntegral_isometry hB _).symm
    _ = _ := integral_congr_ae (by
      filter_upwards [brownianIntegral_elementarySum_ae hB a] with ω hω
      rw [hω])

theorem brownianStepProcess_norm_sq (hB : IsPreBrownianReal B P) {N : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P) :
    (∫ p, brownianStepProcess τ ξ p ^ 2 ∂volume.prod P) =
      ∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val) * ∫ ω, ξ i ω ^ 2 ∂P := by
  calc
    _ = ∫ ω, brownianStepIntegral B τ ξ ω ^ 2 ∂P :=
      brownianElementarySum_isometry hB
        (BrownianIntegralElementary.ofPartition (B := B) (hBm := hBm) (P := P) τ hτ ξ hξ hξ2)
    _ = _ := brownianStepIntegral_isometry hB hBm τ hτ ξ hξ hξ2

theorem brownianStepIntegral_eq_of_process_ae (hB : IsPreBrownianReal B P) {N M : ℕ}
    (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hξ2 : ∀ i, MemLp (ξ i) 2 P)
    (σ : Fin (M + 1) → ℝ≥0) (hσ : Monotone σ) (η : Fin M → Ω → ℝ)
    (hη : ∀ j, StronglyMeasurable[brownianNaturalFiltration B hBm (σ j.castSucc)] (η j))
    (hη2 : ∀ j, MemLp (η j) 2 P)
    (heq : brownianStepProcess τ ξ =ᵐ[volume.prod P] brownianStepProcess σ η) :
    brownianStepIntegral B τ ξ =ᵐ[P] brownianStepIntegral B σ η :=
  brownianElementarySums_integral_eq_of_ae hB
    (BrownianIntegralElementary.ofPartition (B := B) (hBm := hBm) (P := P) τ hτ ξ hξ hξ2)
    (BrownianIntegralElementary.ofPartition (B := B) (hBm := hBm) (P := P) σ hσ η hη hη2) heq

end TimeTraps.Probability

end
