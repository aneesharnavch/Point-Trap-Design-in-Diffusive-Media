module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Support

@[expose] public section

/-! The actual Stieltjes measure of a continuous nondecreasing function
has no atoms. Local constancy gives a null neighborhood and excludes the
point from the topological support of this measure. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

def continuousStieltjesFunction (f : ℝ → ℝ) (hm : Monotone f) (hc : Continuous f) :
    StieltjesFunction ℝ where
  toFun := f
  mono' := hm
  right_continuous' := fun _ => hc.continuousAt.continuousWithinAt

theorem continuousStieltjesFunction_measure_Ioc (f : ℝ → ℝ) (hm : Monotone f)
    (hc : Continuous f) (s t : ℝ) :
    (continuousStieltjesFunction f hm hc).measure (Ioc s t) = ENNReal.ofReal (f t - f s) :=
  (continuousStieltjesFunction f hm hc).measure_Ioc s t

theorem continuousStieltjesFunction_measure_singleton (f : ℝ → ℝ) (hm : Monotone f)
    (hc : Continuous f) (t : ℝ) :
    (continuousStieltjesFunction f hm hc).measure {t} = 0 := by
  rw [StieltjesFunction.measure_singleton]
  change ENNReal.ofReal (f t - Function.leftLim f t) = 0
  rw [hc.continuousAt.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

theorem continuousStieltjesFunction_notMem_support (f : ℝ → ℝ) (hm : Monotone f)
    (hc : Continuous f) (t : ℝ) (hflat : ∀ᶠ s in 𝓝 t, f s = f t) :
    t ∉ (continuousStieltjesFunction f hm hc).measure.support := by
  obtain ⟨s, u, ht, hN, hs⟩ := exists_Icc_mem_subset_of_mem_nhds hflat
  have hsu : s ≤ u := ht.1.trans ht.2
  have hz : (continuousStieltjesFunction f hm hc).measure (Icc s u) = 0 := by
    rw [StieltjesFunction.measure_Icc]
    change ENNReal.ofReal (f u - Function.leftLim f s) = 0
    rw [hc.continuousAt.continuousWithinAt.leftLim_eq]
    rw [hs ⟨hsu, le_rfl⟩, hs ⟨le_rfl, hsu⟩, sub_self, ENNReal.ofReal_zero]
  exact Measure.notMem_support_iff_exists.mpr ⟨Icc s u, hN, hz⟩

end TimeTraps.Analysis
