module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Disjoint

@[expose] public section

/-! Increasing finite horizons exhaust a nonnegative running cost.
The result allows infinite total mass and assumes no integrability. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

theorem nonnegativeRunningCost_iSup (μ : Measure Ω) (f : ℝ × Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, (∫⁻ r in Ioi (0 : ℝ), f (r, p)) ∂μ) =
      ⨆ n : ℕ, ∫⁻ p, (∫⁻ r in Ioc (0 : ℝ) (n : ℝ), f (r, p)) ∂μ := by
  have hs : Monotone (fun n : ℕ => Ioc (0 : ℝ) (n : ℝ)) :=
    fun _ _ h => Ioc_subset_Ioc_right (Nat.cast_le.mpr h)
  have hu : (⋃ n : ℕ, Ioc (0 : ℝ) (n : ℝ)) = Ioi 0 :=
    iUnion_Ioc_eq_Ioi_self_iff.mpr (fun r _ => exists_nat_ge r)
  have he (p : Ω) : (∫⁻ r in Ioi (0 : ℝ), f (r, p)) =
      ⨆ n : ℕ, ∫⁻ r in Ioc (0 : ℝ) (n : ℝ), f (r, p) := by
    rw [← hu]
    exact setLIntegral_iUnion_of_directed _ hs.directed_le
  have hm (n : ℕ) : Measurable (fun p => ∫⁻ r in Ioc (0 : ℝ) (n : ℝ), f (r, p)) :=
    hf.lintegral_prod_left'
  have hmono : Monotone (fun n : ℕ => fun p => ∫⁻ r in Ioc (0 : ℝ) (n : ℝ), f (r, p)) :=
    fun n m h p => lintegral_mono' (Measure.restrict_mono_set volume (hs h)) le_rfl
  simp_rw [he]
  exact lintegral_iSup hm hmono

theorem nonnegativeRunningCost_tendsto (μ : Measure Ω) (f : ℝ × Ω → ℝ≥0∞) (hf : Measurable f) :
    Tendsto (fun n : ℕ => ∫⁻ p, (∫⁻ r in Ioc (0 : ℝ) (n : ℝ), f (r, p)) ∂μ) atTop
      (𝓝 (∫⁻ p, (∫⁻ r in Ioi (0 : ℝ), f (r, p)) ∂μ)) := by
  rw [nonnegativeRunningCost_iSup μ f hf]
  apply tendsto_atTop_iSup
  intro n m h
  apply lintegral_mono
  intro p
  exact lintegral_mono' (Measure.restrict_mono_set volume (Ioc_subset_Ioc_right (Nat.cast_le.mpr h))) le_rfl

end TimeTraps.Probability
