module

public import TimeTraps.Probability.BrownianIntegralPastMultiplierStepData

@[expose] public section

/-! Exact coefficients and stochastic sums for finite original-filtration
step multipliers acting on an arbitrary completed driver integrand. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
variable {hBm : ∀ t, Measurable (B t)} {P : Measure Ω} {M : ℝ≥0}

theorem brownianIntegralSpace_sum_coe {I : Type*} [Fintype I]
    (A : I → brownianIntegralSpace B hBm P) (a : I → ℝ × Ω → ℝ)
    (hA : ∀ i, (A i : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] a i) :
    ((∑ i, A i : brownianIntegralSpace B hBm P) : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => ∑ i, a i p) := by
  have he : ((∑ i, A i : brownianIntegralSpace B hBm P) : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =
      ∑ i, (A i : Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
    change (brownianIntegralSpace B hBm P).subtype (∑ i, A i) = _
    rw [map_sum]
    rfl
  rw [he]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => (A i : Lp ℝ 2 ((volume : Measure ℝ).prod P))), ae_all_iff.mpr hA] with p hs hp
  rw [hs]
  exact Finset.sum_congr rfl (fun i _ => hp i)

theorem brownianPastStepIntegrand_coe {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i : Fin N, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hb : ∀ i ω, |ξ i ω| ≤ M.val) (f : brownianIntegralSpace B hBm P) :
    let S : brownianIntegralSpace B hBm P := @brownianPastStepIntegrand Ω mΩ B hBm P M N τ hτ ξ hξ hb f
    (S : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => brownianStepProcess τ ξ p * (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) := by
  dsimp only
  let A : Fin N → brownianIntegralSpace B hBm P := fun i => brownianPastWindowIntegrand (hτ (Fin.castSucc_le_succ i)) (hξ i) (hb i) f
  change ((∑ i, A i : brownianIntegralSpace B hBm P) : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] _
  refine (brownianIntegralSpace_sum_coe A
    (fun i p => brownianElementaryProcess (τ i.castSucc) (τ i.succ) (ξ i) p *
      (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p)
    (fun i => brownianPastWindowIntegrand_coe (hτ (Fin.castSucc_le_succ i)) (hξ i) (hb i) f)).trans ?_
  filter_upwards [] with p
  rw [← Finset.sum_mul]
  rfl

theorem brownianPastStepIntegrand_integral_ae (hB : IsPreBrownianReal B P)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i : Fin N, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hb : ∀ i ω, |ξ i ω| ≤ M.val) (f : brownianIntegralSpace B hBm P) :
    brownianIntegral hB (@brownianPastStepIntegrand Ω mΩ B hBm P M N τ hτ ξ hξ hb f) =ᵐ[P]
      brownianStepIntegral (fun t ω => brownianIntegralUpTo hB t f ω) τ ξ := by
  let A : Fin N → brownianIntegralSpace B hBm P := fun i => brownianPastWindowIntegrand (hτ (Fin.castSucc_le_succ i)) (hξ i) (hb i) f
  change brownianIntegral hB (∑ i, A i) =ᵐ[P] _
  rw [map_sum]
  have hall : ∀ᵐ ω ∂P, ∀ i, brownianIntegral hB (A i) ω =
      ξ i ω * (brownianIntegralUpTo hB (τ i.succ) f ω - brownianIntegralUpTo hB (τ i.castSucc) f ω) :=
    ae_all_iff.mpr (fun i => brownianPastWindowIntegrand_integral_ae hB
      (hτ (Fin.castSucc_le_succ i)) (hξ i) (hb i) f)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => brownianIntegral hB (A i)), hall]
    with ω hs hω
  rw [hs]
  exact Finset.sum_congr rfl (fun i _ => hω i)

end TimeTraps.Probability

end
