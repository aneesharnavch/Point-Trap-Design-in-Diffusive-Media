module

public import TimeTraps.Analysis.CompactSpectralSemigroupSmoothingNorm
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorDerivative
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

/-! Every Hilbert initial state gives a differentiable heat trajectory at
every positive time. A positive half-time first regularizes the state into
the actual inverse domain, where the proved generator derivative applies.
No domain assumption is imposed on the initial state. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.heatCurve_mem_domain_of_pos {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) {t : ℝ} (ht : 0 < t) :
    h.heatCurve x t ∈ (inverseOperator T h.injective).domain :=
  h.heatSemigroup_mem_domain_of_pos t.toNNReal (Real.toNNReal_pos.mpr ht) x

theorem CompactPositiveInverse.heatCurve_add {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    h.heatCurve x (s + t) = h.heatCurve (h.heatCurve x t) s := by
  simp only [CompactPositiveInverse.heatCurve, Real.toNNReal_add hs ht,
    h.heatSemigroup_add, ContinuousLinearMap.comp_apply]

theorem CompactPositiveInverse.heatCurve_sub_add {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    h.heatCurve (h.heatCurve x a) (t - a) = h.heatCurve x t := by
  rw [← h.heatCurve_add x (sub_nonneg.mpr hat) ha, sub_add_cancel]

theorem CompactPositiveInverse.heatCurve_hasDerivAt_of_pos {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (h.heatCurve x)
      (-inverseOperator T h.injective
        ⟨h.heatCurve x s, h.heatCurve_mem_domain_of_pos x hs⟩) s := by
  let a : ℝ := s / 2
  have ha : 0 < a := half_pos hs
  have has : a < s := half_lt_self hs
  let y : (inverseOperator T h.injective).domain :=
    ⟨h.heatCurve x a, h.heatCurve_mem_domain_of_pos x ha⟩
  have hd := (h.heatCurve_hasDerivAt y (sub_pos.mpr has)).comp_sub_const s a
  have he : h.heatCurve x =ᶠ[𝓝 s] (fun t => h.heatCurve (y : E) (t - a)) := by
    filter_upwards [Ioi_mem_nhds has] with t ht
    exact (h.heatCurve_sub_add x ha.le ht.le).symm
  have hy : (⟨h.heatCurve (y : E) (s - a), h.heatCurve_mem_inverse_domain y (s - a)⟩ :
      (inverseOperator T h.injective).domain) =
      ⟨h.heatCurve x s, h.heatCurve_mem_domain_of_pos x hs⟩ :=
    Subtype.ext (h.heatCurve_sub_add x ha.le has.le)
  rw [hy] at hd
  exact hd.congr_of_eventuallyEq he

theorem CompactPositiveInverse.heatCurve_deriv_of_pos {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) {s : ℝ} (hs : 0 < s) :
    deriv (h.heatCurve x) s = -inverseOperator T h.injective
      ⟨h.heatCurve x s, h.heatCurve_mem_domain_of_pos x hs⟩ :=
  (h.heatCurve_hasDerivAt_of_pos x hs).deriv

theorem CompactPositiveInverse.heatCurve_deriv_norm_le {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) {s : ℝ} (hs : 0 < s) :
    ‖deriv (h.heatCurve x) s‖ ≤ ‖x‖ / s := by
  rw [h.heatCurve_deriv_of_pos x hs, norm_neg]
  simpa only [CompactPositiveInverse.heatCurve, Real.coe_toNNReal s hs.le] using
    h.inverse_heat_norm_le s.toNNReal (Real.toNNReal_pos.mpr hs) x

theorem CompactPositiveInverse.heatCurve_graph_deriv_of_pos {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) {s : ℝ} (hs : 0 < s) :
    (h.heatCurve x s, -deriv (h.heatCurve x) s) ∈ (inverseOperator T h.injective).graph := by
  rw [h.heatCurve_deriv_of_pos x hs, neg_neg]
  exact (inverseOperator T h.injective).mem_graph
    ⟨h.heatCurve x s, h.heatCurve_mem_domain_of_pos x hs⟩

end TimeTraps.Analysis
