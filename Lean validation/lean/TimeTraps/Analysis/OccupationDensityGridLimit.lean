module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

/-! A bounded monotone sequence of real density samples has a finite
extended-real limsup. Its real reconstruction has the supremum density,
and monotone convergence identifies its actual measure on every measurable
set. The order and bound hypotheses may hold only almost everywhere. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

noncomputable def occupationDensityLimit (f : ℕ → α → ℝ) (a : α) : ℝ :=
  (limsup (fun n => ENNReal.ofReal (f n a)) atTop).toReal

theorem occupationDensityLimit_measurable {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n)) : Measurable (occupationDensityLimit f) :=
  (Measurable.limsup (fun n => (hf n).ennreal_ofReal)).ennreal_toReal

omit [MeasurableSpace α] in
theorem occupationDensityLimit_nonneg (f : ℕ → α → ℝ) (a : α) :
    0 ≤ occupationDensityLimit f a := ENNReal.toReal_nonneg

omit [MeasurableSpace α] in
theorem occupationDensityLimit_ofReal_eq_iSup {f : ℕ → α → ℝ} {a : α}
    (hm : Monotone (fun n => f n a)) (hb : ∃ C : ℝ, ∀ n, f n a ≤ C) :
    ENNReal.ofReal (occupationDensityLimit f a) = ⨆ n, ENNReal.ofReal (f n a) := by
  obtain ⟨C, hC⟩ := hb
  have hmono : Monotone (fun n => ENNReal.ofReal (f n a)) :=
    fun i j hij => ENNReal.ofReal_le_ofReal (hm hij)
  have hfinite : (⨆ n, ENNReal.ofReal (f n a)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun n => ENNReal.ofReal_le_ofReal (hC n))
  unfold occupationDensityLimit
  rw [(tendsto_atTop_iSup hmono).limsup_eq, ENNReal.ofReal_toReal hfinite]

theorem occupationDensityLimit_withDensity_apply {f : ℕ → α → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hm : ∀ᵐ a ∂μ, Monotone (fun n => f n a))
    (hb : ∀ᵐ a ∂μ, ∃ C : ℝ, ∀ n, f n a ≤ C)
    {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity (fun a => ENNReal.ofReal (occupationDensityLimit f a)) s =
      ⨆ n, μ.withDensity (fun a => ENNReal.ofReal (f n a)) s := by
  rw [withDensity_apply _ hs]
  calc
    _ = ∫⁻ a in s, ⨆ n, ENNReal.ofReal (f n a) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hm, ae_restrict_of_ae hb] with a ha hba
      exact occupationDensityLimit_ofReal_eq_iSup ha hba
    _ = ⨆ n, ∫⁻ a in s, ENNReal.ofReal (f n a) ∂μ := by
      apply lintegral_iSup' (fun n => (hf n).ennreal_ofReal.aemeasurable)
      filter_upwards [ae_restrict_of_ae hm] with a ha
      exact fun i j hij => ENNReal.ofReal_le_ofReal (ha hij)
    _ = _ := iSup_congr fun n => (withDensity_apply _ hs).symm

end TimeTraps.Analysis
