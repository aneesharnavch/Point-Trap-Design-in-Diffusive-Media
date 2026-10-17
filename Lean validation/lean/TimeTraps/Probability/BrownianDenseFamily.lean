module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The existing Brownian Gaussian projective family pulled back to any
sequence of nonnegative times. Repeated times are retained, with their exact
degenerate Gaussian joint law. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable def brownianTimeProjection (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    (I.image τ → ℝ) → (I → ℝ) :=
  fun x i => x ⟨τ i, Finset.mem_image.mpr ⟨i, i.prop, rfl⟩⟩

theorem brownianTimeProjection_measurable (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    Measurable (brownianTimeProjection τ I) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

noncomputable def brownianSequenceFamily (τ : ℕ → ℝ≥0) (I : Finset ℕ) : Measure (I → ℝ) :=
  (BrownianReal.projectiveFamily (I.image τ)).map (brownianTimeProjection τ I)

instance brownianSequenceFamily_probability (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    IsProbabilityMeasure (brownianSequenceFamily τ I) :=
  Measure.isProbabilityMeasure_map (brownianTimeProjection_measurable τ I).aemeasurable

theorem brownianTimeProjection_restrict (τ : ℕ → ℝ≥0) {I J : Finset ℕ} (hJI : J ⊆ I) :
    Finset.restrict₂ (π := fun _ => ℝ) hJI ∘ brownianTimeProjection τ I =
      brownianTimeProjection τ J ∘
        Finset.restrict₂ (π := fun _ => ℝ) (Finset.image_subset_image hJI) := by
  funext x i
  rfl

theorem brownianSequenceFamily_projective (τ : ℕ → ℝ≥0) :
    IsProjectiveMeasureFamily (α := fun _ => ℝ) (brownianSequenceFamily τ) := by
  intro I J hJI
  unfold brownianSequenceFamily
  rw [Measure.map_map (f := brownianTimeProjection τ I)
      (g := Finset.restrict₂ (π := fun _ : ℕ => ℝ) hJI)
      (Finset.measurable_restrict₂ hJI) (brownianTimeProjection_measurable τ I),
    brownianTimeProjection_restrict τ hJI,
    ← Measure.map_map (brownianTimeProjection_measurable τ J)
      (Finset.measurable_restrict₂ (Finset.image_subset_image hJI)),
    ← BrownianReal.isProjectiveMeasureFamily_projectiveFamily
      (I.image τ) (J.image τ) (Finset.image_subset_image hJI)]

theorem brownianSequenceFamily_eval (τ : ℕ → ℝ≥0) (I : Finset ℕ) (i : I) :
    (brownianSequenceFamily τ I).map (fun x => x i) = gaussianReal 0 (τ i) := by
  rw [brownianSequenceFamily, Measure.map_map (measurable_pi_apply i)
    (brownianTimeProjection_measurable τ I)]
  exact (BrownianReal.measurePreserving_eval_projectiveFamily
    (⟨τ i, Finset.mem_image.mpr ⟨i, i.prop, rfl⟩⟩ : I.image τ)).map_eq

theorem brownianSequenceFamily_increment (τ : ℕ → ℝ≥0) (I : Finset ℕ) (i j : I) :
    (brownianSequenceFamily τ I).map (fun x => x i - x j) =
      gaussianReal 0 (nndist (τ i).val (τ j).val) := by
  rw [brownianSequenceFamily, Measure.map_map (by fun_prop)
    (brownianTimeProjection_measurable τ I)]
  exact (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily (I.image τ)
    ⟨τ i, Finset.mem_image.mpr ⟨i, i.prop, rfl⟩⟩
    ⟨τ j, Finset.mem_image.mpr ⟨j, j.prop, rfl⟩⟩).map_eq

end TimeTraps.Probability
