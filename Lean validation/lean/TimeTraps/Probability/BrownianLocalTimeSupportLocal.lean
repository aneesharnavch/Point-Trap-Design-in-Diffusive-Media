module

public import TimeTraps.Probability.BrownianLocalTimeSupportReal

@[expose] public section

/-! On the same fixed-level full-measure event, the actual global Tanaka
path is locally constant at every time at which the Brownian path is not
at the level. Neighborhoods in nonnegative time handle zero one-sidedly. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem brownianLocalTimeSupportRegular_locally_constant {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeSupportRegular a ω) (t : ℝ≥0)
    (hne : brownianDyadicPath t ω ≠ a) :
    ∀ᶠ s in 𝓝 t, brownianLocalTimeGlobalPath a s ω = brownianLocalTimeGlobalPath a t ω := by
  let δ := |brownianDyadicPath t ω - a| / 2
  have hp : 0 < |brownianDyadicPath t ω - a| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hδ : 0 < δ := half_pos hp
  have hb : Continuous (fun s => brownianDyadicPath s ω) :=
    BrownianDyadicRegular.continuous hω.1
  have hc : Continuous (fun s => |brownianDyadicPath s ω - a|) :=
    (hb.sub continuous_const).abs
  have hn : {s | δ ≤ |brownianDyadicPath s ω - a|} ∈ 𝓝 t := by
    apply Filter.mem_of_superset ((isOpen_lt continuous_const hc).mem_nhds
      (show δ < |brownianDyadicPath t ω - a| from half_lt_self hp))
    intro s hs
    exact (show δ < |brownianDyadicPath s ω - a| from hs).le
  obtain ⟨S, T, ht, hN, hs⟩ := exists_Icc_mem_subset_of_mem_nhds hn
  have hflat := brownianLocalTimeSupportRegular_flat_real hω (ht.1.trans ht.2) hδ
    (fun s hst => hs hst)
  filter_upwards [hN] with s hst
  exact (hflat s hst).trans (hflat t ht).symm

theorem brownianLocalTimeGlobalPath_locally_constant_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, brownianDyadicPath t ω ≠ a →
      ∀ᶠ s in 𝓝 t, brownianLocalTimeGlobalPath a s ω = brownianLocalTimeGlobalPath a t ω :=
  (brownianLocalTimeSupportRegular_ae a).mono (fun _ hω t ht =>
    brownianLocalTimeSupportRegular_locally_constant hω t ht)

end TimeTraps.Probability
