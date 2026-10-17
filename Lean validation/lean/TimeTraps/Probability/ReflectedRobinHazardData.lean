module

public import TimeTraps.Probability.ReflectedAtomicHazardData

@[expose] public section

/-! Reactive endpoints use the actual folded-path regulators. Their
normalization is derived from the literal doubled endpoint correction:
for variance 2D the endpoint coefficient is K/D. Thus the physical Robin
hazard has endpoint terms (betaLeft/D) K0 and (betaRight/D) KL. The finite
interior label type may be empty. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

def reflectedRobinSite (L : ℝ) (a : ι → ℝ) : ι ⊕ Bool → ℝ :=
  Sum.elim a (fun b => if b then L else 0)

def reflectedRobinStrength (κ : ι → ℝ) (β₀ βL : ℝ) : ι ⊕ Bool → ℝ :=
  Sum.elim κ (fun b => if b then βL else β₀)

def reflectedRobinHazard (L D x : ℝ) (a κ : ι → ℝ) (β₀ βL : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  reflectedAtomicHazard L D x a κ t ω +
    (β₀ / D) * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω +
    (βL / D) * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω

def reflectedRobinSurvival (L D x : ℝ) (a κ : ι → ℝ) (β₀ βL : ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (-reflectedRobinHazard L D x a κ β₀ βL t ω)

theorem reflectedRobin_endpoint_left (x L : ℝ) {D : ℝ} (hD : 0 < D)
    (t : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L 0 t ω =
      affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω / D := by
  rw [reflectedInteriorOccupationCoefficient, reflectedInteriorCorrection_left,
    Real.sq_sqrt (show 0 ≤ 2 * D by positivity)]
  field_simp

theorem reflectedRobin_endpoint_right (x L : ℝ) {D : ℝ} (hD : 0 < D)
    (t : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L L t ω =
      affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω / D := by
  rw [reflectedInteriorOccupationCoefficient, reflectedInteriorCorrection_right,
    Real.sq_sqrt (show 0 ≤ 2 * D by positivity)]
  field_simp

omit [Fintype ι] in
theorem reflectedRobinStrength_nonneg {κ : ι → ℝ} {β₀ βL : ℝ}
    (hκ : ∀ i, 0 ≤ κ i) (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) :
    ∀ i, 0 ≤ reflectedRobinStrength κ β₀ βL i := by
  intro i
  cases i with
  | inl i => exact hκ i
  | inr b => cases b <;> assumption

theorem reflectedRobinHazard_eq_atomic (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (β₀ βL : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedRobinHazard L D x a κ β₀ βL t ω =
      reflectedAtomicHazard L D x (reflectedRobinSite L a)
        (reflectedRobinStrength κ β₀ βL) t ω := by
  unfold reflectedAtomicHazard weightedContactHazard
  rw [Fintype.sum_sum_type]
  simp only [reflectedRobinSite, reflectedRobinStrength, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    reflectedRobin_endpoint_left x L hD, reflectedRobin_endpoint_right x L hD]
  unfold reflectedRobinHazard reflectedAtomicHazard weightedContactHazard
  ring

theorem reflectedRobinSurvival_eq_atomic (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (β₀ βL : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedRobinSurvival L D x a κ β₀ βL t ω =
      reflectedAtomicSurvival L D x (reflectedRobinSite L a)
        (reflectedRobinStrength κ β₀ βL) t ω := by
  rw [reflectedRobinSurvival, reflectedAtomicSurvival, reflectedRobinHazard_eq_atomic L hD]

theorem reflectedRobinHazard_jointlyMeasurable (L D x : ℝ) (a κ : ι → ℝ) (β₀ βL : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedRobinHazard L D x a κ β₀ βL p.1 p.2) :=
  ((reflectedAtomicHazard_jointlyMeasurable L D x a κ).add
    ((affineBrownianRegulator_time_jointlyMeasurable x (Real.sqrt (2 * D)) L 0).const_mul _)).add
    ((affineBrownianRegulator_time_jointlyMeasurable x (Real.sqrt (2 * D)) L 1).const_mul _)

theorem reflectedRobinSurvival_jointlyMeasurable (L D x : ℝ) (a κ : ι → ℝ) (β₀ βL : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedRobinSurvival L D x a κ β₀ βL p.1 p.2) :=
  (reflectedRobinHazard_jointlyMeasurable L D x a κ β₀ βL).neg.exp

end TimeTraps.Probability

end
