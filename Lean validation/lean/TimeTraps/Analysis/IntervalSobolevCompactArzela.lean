module

public import TimeTraps.Analysis.IntervalSobolevCompactEmbedding
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

@[expose] public section

/-! Compactness of the actual Sobolev representative map. Trace bounds
give a fixed compact range on each norm ball, and the energy half-Hölder
estimate gives equicontinuity. Arzelà–Ascoli then proves compact closure
in the uniform norm, with no compactness assumption on Sobolev balls. -/

namespace TimeTraps.Analysis.IntervalSobolevSpace

open Set MeasureTheory Filter Metric
open scoped Topology

theorem toContinuousL_closedBall_compact {l r : ℝ} (hlr : l < r) (R : ℝ) :
    IsCompact (closure (toContinuousL hlr '' closedBall 0 R)) := by
  let e := (ContinuousMap.isometryEquivBoundedOfCompact (Icc l r) ℝ).toHomeomorph
  let A : Set (BoundedContinuousFunction (Icc l r) ℝ) :=
    (fun u => e (toContinuousL hlr u)) '' closedBall 0 R
  let C : ℝ := Real.sqrt (2 / (r - l) + 2 * (r - l))
  have hrange : ∀ (f : BoundedContinuousFunction (Icc l r) ℝ) (x : Icc l r), f ∈ A →
      f x ∈ Icc (-(C * R)) (C * R) := by
    intro f x hf
    obtain ⟨u, hu, rfl⟩ := hf
    have hnorm : ‖u‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hu
    change u.representative hlr x ∈ Icc (-(C * R)) (C * R)
    exact abs_le.mp ((representative_abs_le u hlr x.property).trans
      (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)))
  have hequi : Equicontinuous ((↑) : A → Icc l r → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply Metric.uniformEquicontinuous_of_continuity_modulus (fun t => Real.sqrt t * R)
    · have hc : Continuous (fun t : ℝ => Real.sqrt t * R) := by fun_prop
      simpa only [Real.sqrt_zero, zero_mul] using hc.tendsto (0 : ℝ)
    · intro x y f
      obtain ⟨u, hu, huf⟩ := f.property
      have hnorm : ‖u‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hu
      change dist (f.val x) (f.val y) ≤ Real.sqrt (dist x y) * R
      rw [← huf]
      change dist (toContinuousL hlr u x) (toContinuousL hlr u y) ≤ _
      exact (toContinuousL_dist_le hlr u x y).trans
        (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _))
  have hA : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-(C * R)) (C * R)) isCompact_Icc A hrange hequi
  have hc := hA.image e.symm.continuous
  rw [e.symm.image_closure] at hc
  simpa only [A, image_image, Function.comp_def, e.symm_apply_apply] using hc

theorem toContinuousL_isCompact {l r : ℝ} (hlr : l < r) :
    IsCompactOperator (toContinuousL hlr) := by
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).mpr
  exact ⟨closedBall 0 1, closedBall_mem_nhds _ zero_lt_one,
    toContinuousL_closedBall_compact hlr 1⟩

theorem toContinuousL_bounded_compact {l r : ℝ} (hlr : l < r)
    {S : Set (IntervalSobolevSpace l r)} (hS : Bornology.IsBounded S) :
    IsCompact (closure (toContinuousL hlr '' S)) :=
  (toContinuousL_isCompact hlr).isCompact_closure_image_of_bounded hS

end TimeTraps.Analysis.IntervalSobolevSpace
