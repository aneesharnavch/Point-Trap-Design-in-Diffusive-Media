module

public import TimeTraps.Probability.ReflectedAtomicSurvivalExpectation
public import TimeTraps.Probability.ReflectedFiniteKinkC2Moments

@[expose] public section

/-! Actual survival-weighted continuous spatial tests. The needed bound
is derived on the compact reflected range; no global boundedness of the
test and no eventual killing hypothesis is required. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {ι : Type*} [Fintype ι] {V : ℝ → ℝ}

noncomputable def reflectedAtomicValueMap (hV : Continuous V) (L : ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun y => V y.val, hV.comp continuous_subtype_val⟩

noncomputable def reflectedAtomicWeightedValue (V : ℝ → ℝ) (L D x : ℝ)
    (a κ : ι → ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  reflectedAtomicSurvival L D x a κ t ω * V (foldedTrajectory L D x brownianDyadicPath t ω)

noncomputable def reflectedAtomicValueExpectation (V : ℝ → ℝ) (L D x : ℝ)
    (a κ : ι → ℝ) (t : ℝ≥0) : ℝ :=
  ∫ ω, reflectedAtomicWeightedValue V L D x a κ t ω ∂brownianDyadicMeasure

theorem reflectedAtomicWeightedValue_jointlyMeasurable (hV : Continuous V)
    (L D x : ℝ) (a κ : ι → ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedAtomicWeightedValue V L D x a κ p.1 p.2) := by
  exact (reflectedAtomicSurvival_jointlyMeasurable L D x a κ).mul
    (hV.measurable.comp (foldedTrajectory_joint_measurable L D x brownianDyadicPath
      brownianDyadicPath_jointly_measurable))

theorem reflectedAtomicWeightedValue_bound (hV : Continuous V)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (t : ℝ≥0) (ω : ℕ → ℝ) :
    ‖reflectedAtomicWeightedValue V L D x a κ t ω‖ ≤ ‖reflectedAtomicValueMap hV L‖ := by
  have hw := reflectedAtomicSurvival_bounds L hD x a κ hκ t ω
  have hv := (reflectedAtomicValueMap hV L).norm_coe_le_norm
    ⟨foldedTrajectory L D x brownianDyadicPath t ω,
      foldedTrajectory_mem L hL D x brownianDyadicPath t ω⟩
  change ‖V (foldedTrajectory L D x brownianDyadicPath t ω)‖ ≤ ‖reflectedAtomicValueMap hV L‖ at hv
  change ‖reflectedAtomicSurvival L D x a κ t ω *
    V (foldedTrajectory L D x brownianDyadicPath t ω)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hw.1]
  exact (mul_le_mul_of_nonneg_right hw.2 (norm_nonneg _)).trans (by simpa using hv)

theorem reflectedAtomicWeightedValue_memLp (hV : Continuous V)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (t : ℝ≥0) :
    MemLp (reflectedAtomicWeightedValue V L D x a κ t) 2 brownianDyadicMeasure := by
  have hm := (reflectedAtomicWeightedValue_jointlyMeasurable hV L D x a κ).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ω : ℕ → ℝ => (t, ω)))
  apply MemLp.of_bound hm.aestronglyMeasurable ‖reflectedAtomicValueMap hV L‖
  exact Eventually.of_forall (fun ω => by
    change |reflectedAtomicWeightedValue V L D x a κ t ω| ≤ ‖reflectedAtomicValueMap hV L‖
    simpa only [Real.norm_eq_abs] using reflectedAtomicWeightedValue_bound hV L hL D hD x a κ hκ t ω)

theorem reflectedAtomicValueExpectation_continuous (hV : Continuous V)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) : Continuous (reflectedAtomicValueExpectation V L D x a κ) := by
  apply continuous_of_dominated
    (fun t => (reflectedAtomicWeightedValue_memLp hV L hL D hD x a κ hκ t).aestronglyMeasurable)
    (bound := fun _ => ‖reflectedAtomicValueMap hV L‖)
  · intro t
    exact Eventually.of_forall (reflectedAtomicWeightedValue_bound hV L hL D hD x a κ hκ t)
  · exact integrable_const _
  · filter_upwards [reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ,
      brownianDyadicPath_continuous_ae] with ω hw hb
    have hx : Continuous (fun t => foldedTrajectory L D x brownianDyadicPath t ω) :=
      (reflectedFold_continuous L).comp (continuous_const.add (continuous_const.mul hb))
    exact hw.2.2.2.1.mul (hV.comp hx)

end TimeTraps.Probability
