module

public import TimeTraps.Probability.BrownianIntegralPastMultiplierPullOut
public import TimeTraps.Probability.BrownianIntegralMartingaleIncrements

@[expose] public section

/-! Finite left-adapted association with an actual completed Brownian
integral. A step coefficient times a driver integrand integrates to the
literal sum of that coefficient times the driver's increments, always in
the original Brownian filtration. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
variable {hBm : ∀ t, Measurable (B t)} {P : Measure Ω} {M : ℝ≥0}

theorem brownianPastWindow_mem_future {s t : ℝ≥0} (hst : s ≤ t)
    (f : brownianIntegralSpace B hBm P) :
    brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f ∈
      brownianIntegralFutureSpace B hBm P s := by
  apply brownianIntegral_mem_future_of_cutoff_zero
  rw [map_sub, brownianTimeCutoff_comp, brownianTimeCutoff_comp, min_eq_left hst, min_self, sub_self]

def brownianPastWindowIntegrand {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (f : brownianIntegralSpace B hBm P) :
    brownianIntegralSpace B hBm P :=
  brownianPastMultiplier hZ hb ⟨brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f,
    brownianPastWindow_mem_future hst f⟩

theorem brownianPastWindowIntegrand_coe {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (f : brownianIntegralSpace B hBm P) :
    (brownianPastWindowIntegrand hst hZ hb f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => brownianElementaryProcess s t Z p * (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) := by
  unfold brownianPastWindowIntegrand
  filter_upwards [brownianPastMultiplier_coe hZ hb
    ⟨brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f,
      brownianPastWindow_mem_future hst f⟩, brownianTimeCutoff_sub_coe hst f] with p hm hc
  change ((brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f :
    brownianIntegralSpace B hBm P) : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p = _ at hc
  rw [hm, hc]
  change Z p.2 * (brownianTimeWindow s t).indicator (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p =
    ((Ioc s.val t.val).indicator (fun _ => 1) p.1 * Z p.2) * _
  by_cases hp : p.1 ∈ Ioc s.val t.val
  · have hw : p ∈ brownianTimeWindow s t := hp
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hw, one_mul]
  · have hw : p ∉ brownianTimeWindow s t := hp
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hw, mul_zero, zero_mul, zero_mul]

theorem brownianPastWindowIntegrand_integral_ae (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hb : ∀ ω, |Z ω| ≤ M.val) (f : brownianIntegralSpace B hBm P) :
    brownianIntegral hB (brownianPastWindowIntegrand hst hZ hb f) =ᵐ[P]
      (fun ω => Z ω * (brownianIntegralUpTo hB t f ω - brownianIntegralUpTo hB s f ω)) := by
  have h := brownianPastMultiplier_integral_ae hB hZ hb
    ⟨brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f,
      brownianPastWindow_mem_future hst f⟩
  change brownianIntegral hB (brownianPastWindowIntegrand hst hZ hb f) =ᵐ[P]
    (fun ω => Z ω * brownianIntegral hB
      (brownianTimeCutoff B hBm P t f - brownianTimeCutoff B hBm P s f) ω) at h
  rw [map_sub] at h
  filter_upwards [h, Lp.coeFn_sub (brownianIntegralUpTo hB t f)
    (brownianIntegralUpTo hB s f)] with ω hh hs
  rw [hh]
  change Z ω * (brownianIntegralUpTo hB t f - brownianIntegralUpTo hB s f : Lp ℝ 2 P) ω = _
  rw [hs]
  rfl

def brownianPastStepIntegrand {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hb : ∀ i ω, |ξ i ω| ≤ M.val) (f : brownianIntegralSpace B hBm P) :
    brownianIntegralSpace B hBm P :=
  ∑ i, brownianPastWindowIntegrand (hτ (Fin.castSucc_le_succ i)) (hξ i) (hb i) f

end TimeTraps.Probability

end
