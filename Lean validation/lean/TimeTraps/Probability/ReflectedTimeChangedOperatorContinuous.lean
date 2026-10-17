module

public import TimeTraps.Probability.ReflectedPathTimeChangeContinuous
public import TimeTraps.Probability.ReflectedPathOperatorContinuous
public import TimeTraps.Probability.ReflectedBoundedStrongMarkovTimeChangeKernel

@[expose] public section

/-! The actual inverse-clock transition preserves continuous spatial
tests. Its continuity follows from a fixed compact-path realization and
bounded convergence; no Feller property is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal

theorem reflectedTimeChangedPathTest_continuous (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 L)) :
    Continuous (reflectedTimeChangedPathTest L hL H c hc hpos t f) :=
  hf.domRestrict.comp ((reflectedMarkovPathTimeChange_joint_continuous L hL H
    (fun y : Icc (0 : ℝ) L => c y.val) hc.domRestrict (fun y => hpos y.val y.property)).comp
      (continuous_const.prodMk continuous_id))

theorem reflectedTimeChangedOperator_continuous_interval (L : ℝ) (hL : 0 < L) (D : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 L)) :
    Continuous (fun y : Icc (0 : ℝ) L => reflectedTimeChangedOperator L D c t f y.val) := by
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  let m : ℝ≥0 := ⟨c a, (hpos a ha).le⟩
  have hm : 0 < m := hpos a ha
  have hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y := fun y hy => hmin hy
  let F : C(Icc (0 : ℝ) L, ℝ) := ⟨fun y => f y.val, hf.domRestrict⟩
  have he : (fun y : Icc (0 : ℝ) L => reflectedTimeChangedOperator L D c t f y.val) =
      reflectedMarkovPathOperator L hL D (t / m)
        (reflectedTimeChangedPathTest L hL (t / m) c hc hpos t f) := by
    funext y
    exact (reflectedTimeChangedOperator_path L hL D (t / m) c hc hpos m hm hmc t le_rfl f y).symm
  rw [he]
  apply reflectedMarkovPathOperator_continuous L hL D (t / m)
    (reflectedTimeChangedPathTest_continuous L hL (t / m) c hc hpos t hf)
  intro p
  exact F.norm_coe_le_norm _

end TimeTraps.Probability

end
