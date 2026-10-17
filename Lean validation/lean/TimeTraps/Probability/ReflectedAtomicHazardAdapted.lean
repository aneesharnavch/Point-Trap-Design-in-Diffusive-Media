module

public import TimeTraps.Probability.ReflectedAtomicHazardData

@[expose] public section

/-! Fixed-time measurability relative to the original raw Brownian past.
The actual field is transferred through its proved almost-everywhere
local-time version. Countable lattice sums use measurable representatives
and a countable intersection; no strong adaptation of the literal field
or common-time representative identity is asserted. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem brownianLocalTimeTimeField_raw_aestronglyMeasurable (a : ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (brownianLocalTimeTimeField a t)
      brownianDyadicMeasure := by
  have he : brownianLocalTimeTimeField a t =ᵐ[brownianDyadicMeasure] brownianLocalTimeGlobalPath a t :=
    (brownianLocalTimeTimeField_globalPath_ae a).mono (fun _ hω => hω t)
  exact (brownianLocalTimeGlobalPath_raw_aestronglyMeasurable a t).congr he.symm

theorem affineBrownianRegulator_raw_aestronglyMeasurable (x σ L : ℝ) (b : ℤ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (affineBrownianRegulator x σ L b t)
      brownianDyadicMeasure := by
  let f : ℤ → (ℕ → ℝ) → ℝ := fun k =>
    affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) t
  have hf (k : ℤ) : AEStronglyMeasurable[brownianFiltration t] (f k) brownianDyadicMeasure :=
    (brownianLocalTimeTimeField_raw_aestronglyMeasurable
      (((((2 * k + b : ℤ) : ℝ) * L) - x) / σ) t).const_mul σ
  let g : ℤ → (ℕ → ℝ) → ℝ := fun k => (hf k).mk (f k)
  have hg (k : ℤ) : @Measurable (ℕ → ℝ) ℝ (brownianFiltration t) inferInstance (g k) :=
    (hf k).stronglyMeasurable_mk.measurable
  have hs : StronglyMeasurable[brownianFiltration t] (fun ω => ∑' k, g k ω) := by
    let : MeasurableSpace (ℕ → ℝ) := brownianFiltration t
    exact (Measurable.tsum hg).stronglyMeasurable
  refine ⟨fun ω => ∑' k, g k ω, hs, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun k => (hf k).ae_eq_mk)] with ω hω
  exact tsum_congr hω

theorem reflectedInteriorOccupationCoefficient_raw_aestronglyMeasurable
    (x σ L a : ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t]
      (reflectedInteriorOccupationCoefficient x σ L a t) brownianDyadicMeasure := by
  have hm := affineBrownianRegulator_raw_aestronglyMeasurable (x - a) σ L 0 t
  have hp := affineBrownianRegulator_raw_aestronglyMeasurable (x + a) σ L 0 t
  have hd : Continuous (fun z : ℝ => z / σ ^ 2) := continuous_id.div_const _
  have h := hd.comp_aestronglyMeasurable (hm.add hp)
  exact h

theorem reflectedAtomicHazard_raw_aestronglyMeasurable
    (L D x : ℝ) (a κ : ι → ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t]
      (reflectedAtomicHazard L D x a κ t) brownianDyadicMeasure := by
  classical
  have hsum (s : Finset ι) : AEStronglyMeasurable[brownianFiltration t]
      (fun ω => ∑ i ∈ s, κ i *
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) t ω)
        brownianDyadicMeasure := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact aestronglyMeasurable_const
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi, Pi.add_def] using
        ((reflectedInteriorOccupationCoefficient_raw_aestronglyMeasurable
          x (Real.sqrt (2 * D)) L (a i) t).const_mul (κ i)).add ih
  unfold reflectedAtomicHazard weightedContactHazard
  exact hsum Finset.univ

theorem reflectedAtomicSurvival_raw_aestronglyMeasurable
    (L D x : ℝ) (a κ : ι → ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t]
      (reflectedAtomicSurvival L D x a κ t) brownianDyadicMeasure :=
  Real.continuous_exp.comp_aestronglyMeasurable
    (reflectedAtomicHazard_raw_aestronglyMeasurable L D x a κ t).neg

end TimeTraps.Probability
