module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-! Convergence of contractions on a dense range extends to every point.
This is the elementary three-term approximation argument. -/

namespace TimeTraps.Analysis

open Filter
open scoped Topology

theorem contraction_denseRange_tendsto {ι A X : Type*} [PseudoMetricSpace X]
    {l : Filter ι} (F : ι → X → X) (g : A → X) (hg : DenseRange g)
    (hF : ∀ i x y, dist (F i x) (F i y) ≤ dist x y)
    (hlim : ∀ a, Tendsto (fun i => F i (g a)) l (𝓝 (g a))) (x : X) :
    Tendsto (fun i => F i x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp hg x (ε / 4) (by positivity)
  have he := Metric.tendsto_nhds.mp (hlim a) (ε / 4) (by positivity)
  filter_upwards [he] with i hi
  calc
    dist (F i x) x ≤ dist (F i x) (F i (g a)) + dist (F i (g a)) x := dist_triangle _ _ _
    _ ≤ dist x (g a) + (dist (F i (g a)) (g a) + dist (g a) x) :=
      add_le_add (hF i x (g a)) (dist_triangle _ _ _)
    _ < ε := by rw [dist_comm (g a) x]; linarith

theorem contraction_denseRange_tendsto_map {ι A X : Type*} [PseudoMetricSpace X]
    {l : Filter ι} (F : ι → X → X) (H : X → X) (g : A → X) (hg : DenseRange g)
    (hF : ∀ i x y, dist (F i x) (F i y) ≤ dist x y)
    (hH : ∀ x y, dist (H x) (H y) ≤ dist x y)
    (hlim : ∀ a, Tendsto (fun i => F i (g a)) l (𝓝 (H (g a)))) (x : X) :
    Tendsto (fun i => F i x) l (𝓝 (H x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp hg x (ε / 4) (by positivity)
  have he := Metric.tendsto_nhds.mp (hlim a) (ε / 4) (by positivity)
  filter_upwards [he] with i hi
  calc
    dist (F i x) (H x) ≤ dist (F i x) (F i (g a)) + dist (F i (g a)) (H x) :=
      dist_triangle _ _ _
    _ ≤ dist x (g a) + (dist (F i (g a)) (H (g a)) + dist (H (g a)) (H x)) :=
      add_le_add (hF i x (g a)) (dist_triangle _ _ _)
    _ ≤ dist x (g a) + (dist (F i (g a)) (H (g a)) + dist (g a) x) :=
      add_le_add le_rfl (add_le_add le_rfl (hH (g a) x))
    _ < ε := by rw [dist_comm (g a) x]; linarith

theorem contraction_denseRange_continuous {ι A X : Type*}
    [TopologicalSpace ι] [PseudoMetricSpace X]
    (F : ι → X → X) (g : A → X) (hg : DenseRange g)
    (hF : ∀ i x y, dist (F i x) (F i y) ≤ dist x y)
    (hc : ∀ a, Continuous (fun i => F i (g a))) (x : X) :
    Continuous (fun i => F i x) := by
  apply continuous_iff_continuousAt.mpr
  intro i
  exact contraction_denseRange_tendsto_map F (F i) g hg hF (hF i)
    (fun a => (hc a).tendsto i) x

end TimeTraps.Analysis
