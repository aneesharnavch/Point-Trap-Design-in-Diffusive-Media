module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

/-! A finite resolvent decomposition cancels the state part of the
running source pathwise. Only genuine interval integrability is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory
open scoped NNReal

variable {I : Type*} [Fintype I]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


theorem graphResolventCompensated_algebra
    (q r : ℝ≥0 → ℝ) (v l : I → ℝ≥0 → ℝ) (c : I → ℝ) (speed : ℝ≥0 → ℝ)
    (T : ℝ≥0) (hq : Continuous q) (hv : ∀ i, Continuous (v i))
    (hs : IntervalIntegrable (fun s : ℝ => speed s.toNNReal) volume 0 (T : ℝ))
    (hqr : ∀ t, q t = r t - ∑ i, c i * v i t) :
    r T - (∫ s in (0 : ℝ)..T.val, r s.toNNReal) +
        (∫ s in (0 : ℝ)..T.val, q s.toNNReal + speed s.toNNReal) -
      ∑ i, c i * (v i T - (∫ s in (0 : ℝ)..T.val, v i s.toNNReal) + l i T) =
    q T + (∫ s in (0 : ℝ)..T.val, speed s.toNNReal) - ∑ i, c i * l i T := by
  have hiq : IntervalIntegrable (fun s : ℝ => q s.toNNReal) volume 0 T.val :=
    (hq.comp continuous_real_toNNReal).intervalIntegrable (μ := volume) 0 T.val
  have hiv (i) : IntervalIntegrable (fun s : ℝ => v i s.toNNReal) volume 0 T.val :=
    ((hv i).comp continuous_real_toNNReal).intervalIntegrable (μ := volume) 0 T.val
  have his : IntervalIntegrable (fun s : ℝ => ∑ i, c i * v i s.toNNReal) volume 0 T.val := by
    have hi := IntervalIntegrable.sum Finset.univ (fun i _ => (hiv i).const_mul (c i))
    have he : (∑ i, fun s : ℝ => c i * v i s.toNNReal) =
        (fun s : ℝ => ∑ i, c i * v i s.toNNReal) := by
      funext s
      simp only [Finset.sum_apply]
    rw [he] at hi
    exact hi
  have hir : (∫ s in (0 : ℝ)..T.val, r s.toNNReal) =
      (∫ s in (0 : ℝ)..T.val, q s.toNNReal) +
        ∑ i, c i * ∫ s in (0 : ℝ)..T.val, v i s.toNNReal := by
    calc
      _ = ∫ s in (0 : ℝ)..T.val, q s.toNNReal + ∑ i, c i * v i s.toNNReal := by
        apply intervalIntegral.integral_congr
        intro s _
        have hh := hqr s.toNNReal
        linarith
      _ = _ := by
        rw [intervalIntegral.integral_add hiq his,
          intervalIntegral.integral_finsetSum (fun i _ => (hiv i).const_mul (c i))]
        simp only [intervalIntegral.integral_const_mul]
  rw [hir, intervalIntegral.integral_add hiq hs, hqr T]
  simp_rw [mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end TimeTraps.Probability
