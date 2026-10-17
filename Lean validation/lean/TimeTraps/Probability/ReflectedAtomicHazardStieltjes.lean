module

public import TimeTraps.Probability.ReflectedAtomicHazardPaths
public import TimeTraps.Probability.ReflectedInteriorOccupationStieltjesIntegral

@[expose] public section

/-! The actual hazard time measure is the finite nonnegative sum of the
actual occupation time measures. The Stieltjes functions retain the
already proved fallback versions off their individual regular events;
on the finite-label event their sum is the literal hazard. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

def reflectedAtomicHazardStieltjes (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (_hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) : StieltjesFunction ℝ :=
  ∑ i, Real.toNNReal (κ i) • reflectedInteriorOccupationStieltjes x
    (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω

def reflectedAtomicHazardTimeMeasure (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) : Measure ℝ :=
  (reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω).measure

omit [Fintype ι] in
theorem stieltjesFinsetSum_apply (s : Finset ι) (K : ι → StieltjesFunction ℝ) (r : ℝ) :
    (∑ i ∈ s, K i) r = ∑ i ∈ s, K i r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, StieltjesFunction.zero_apply]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, StieltjesFunction.add_apply, ih, Finset.sum_insert hi]

theorem reflectedAtomicHazardStieltjes_coe (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) :
    (reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω : ℝ → ℝ) =
      (fun r => ∑ i, κ i * reflectedInteriorOccupationStieltjes x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω r) := by
  funext r
  unfold reflectedAtomicHazardStieltjes
  rw [stieltjesFinsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.toNNReal (κ i) : ℝ) * _ = _
  rw [Real.coe_toNNReal _ (hκ i)]

theorem reflectedInteriorOccupationStieltjes_continuous (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) :
    Continuous (reflectedInteriorOccupationStieltjes x hσ hL a ω) :=
  continuous_const.mul
    ((affineBrownianRegulatorRealPath_continuous (x - a) hσ hL 0 ω).add
      (affineBrownianRegulatorRealPath_continuous (x + a) hσ hL 0 ω))

theorem reflectedAtomicHazardStieltjes_continuous (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) :
    Continuous (reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω) := by
  rw [reflectedAtomicHazardStieltjes_coe]
  exact continuous_finsetSum Finset.univ (fun i _ =>
    (reflectedInteriorOccupationStieltjes_continuous x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω).const_mul (κ i))

theorem reflectedAtomicHazardStieltjes_apply (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω) (r : ℝ) :
    reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω r =
      reflectedAtomicHazard L D x a κ r.toNNReal ω := by
  rw [show reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω r =
    ∑ i, κ i * reflectedInteriorOccupationStieltjes x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω r from
    congrFun (reflectedAtomicHazardStieltjes_coe L hL D hD x a κ hκ ω) r]
  change (∑ i, κ i * reflectedInteriorOccupationStieltjes x
    (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω r) =
    ∑ i, κ i * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) r.toNNReal ω
  apply Finset.sum_congr rfl
  intro i _
  rw [reflectedInteriorOccupationStieltjes_apply _ hL (hω i)]

theorem reflectedAtomicHazardStieltjes_zero (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω) :
    reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω 0 = 0 := by
  rw [show reflectedAtomicHazardStieltjes L hL D hD x a κ hκ ω 0 =
    ∑ i, κ i * reflectedInteriorOccupationStieltjes x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω 0 from
    congrFun (reflectedAtomicHazardStieltjes_coe L hL D hD x a κ hκ ω) 0]
  apply Finset.sum_eq_zero
  intro i _
  rw [reflectedInteriorOccupationStieltjes_zero _ hL (hω i), mul_zero]

theorem reflectedAtomicHazardTimeMeasure_eq_sum (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (ω : ℕ → ℝ) :
    reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω =
      ∑ i, Real.toNNReal (κ i) • reflectedInteriorOccupationTimeMeasure x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω := by
  classical
  let K : ι → StieltjesFunction ℝ := fun i => Real.toNNReal (κ i) •
    reflectedInteriorOccupationStieltjes x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL (a i) ω
  have hs (s : Finset ι) : (∑ i ∈ s, K i).measure = ∑ i ∈ s, (K i).measure := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, StieltjesFunction.measure_zero]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, StieltjesFunction.measure_add, ih, Finset.sum_insert hi]
  change (∑ i, K i).measure = _
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  exact (StieltjesFunction.measure_smul _ _).trans
    (congrArg (fun μ : Measure ℝ => Real.toNNReal (κ i) • μ)
      (reflectedInteriorOccupationTimeMeasure_eq_stieltjes x _ hL (a i) ω).symm)

theorem reflectedAtomicHazardTimeMeasure_Ioc (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {ω : ℕ → ℝ}
    (hω : ∀ i, reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω) (S T : ℝ) :
    reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω (Ioc S T) =
      ENNReal.ofReal (reflectedAtomicHazard L D x a κ T.toNNReal ω -
        reflectedAtomicHazard L D x a κ S.toNNReal ω) := by
  rw [reflectedAtomicHazardTimeMeasure, StieltjesFunction.measure_Ioc,
    reflectedAtomicHazardStieltjes_apply L hL D hD x a κ hκ hω T,
    reflectedAtomicHazardStieltjes_apply L hL D hD x a κ hκ hω S]

end TimeTraps.Probability

end
