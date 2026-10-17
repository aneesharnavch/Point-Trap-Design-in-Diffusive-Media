module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Tactic

@[expose] public section

/-! Successive disintegration of a projective family of real probability
laws. These are actual Markov kernels, ready for Ionescu--Tulcea extension;
no stochastic process or extension measure is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

abbrev RealPrefix (n : ℕ) := (i : Finset.Iic n) → ℝ

set_option backward.isDefEq.respectTransparency false in
def realPrefixSplit (n : ℕ) : RealPrefix (n + 1) ≃ᵐ RealPrefix n × ℝ where
  toFun x := (frestrictLe₂ (π := fun _ : ℕ => ℝ) (Nat.le_succ n) x,
    x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
  invFun z i := if h : i.val ≤ n then z.1 ⟨i.val, Finset.mem_Iic.mpr h⟩ else z.2
  left_inv x := by
    funext i
    dsimp only
    split_ifs with hi
    · rfl
    · have hv : i.val = n + 1 := by
        have := Finset.mem_Iic.mp i.prop
        omega
      have he : i = (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1)) := Subtype.ext hv
      rw [he]
  right_inv z := by
    apply Prod.ext
    · funext i
      simp [frestrictLe₂, Finset.mem_Iic.mp i.prop]
    · simp
  measurable_toFun := by
    change Measurable (fun x : RealPrefix (n + 1) =>
      (frestrictLe₂ (π := fun _ : ℕ => ℝ) (Nat.le_succ n) x,
        x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩))
    exact (measurable_frestrictLe₂ (X := fun _ : ℕ => ℝ) (Nat.le_succ n)).prodMk
      (measurable_pi_apply (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1)))
  measurable_invFun := by
    change Measurable (fun z : RealPrefix n × ℝ => fun i : Finset.Iic (n + 1) =>
      if h : i.val ≤ n then z.1 ⟨i.val, Finset.mem_Iic.mpr h⟩ else z.2)
    refine measurable_pi_lambda _ fun i => ?_
    by_cases hi : i.val ≤ n
    · simpa only [hi, dite_true, Function.comp_def] using
        (measurable_pi_apply (⟨i.val, Finset.mem_Iic.mpr hi⟩ : Finset.Iic n)).comp measurable_fst
    · simpa only [hi, dite_false] using measurable_snd

theorem realPrefixSplit_fst (n : ℕ) :
    Prod.fst ∘ realPrefixSplit n = frestrictLe₂ (π := fun _ : ℕ => ℝ) (Nat.le_succ n) := rfl

theorem realPrefixSplit_restrict (n : ℕ) :
    realPrefixSplit n ∘ (frestrictLe (π := fun _ : ℕ => ℝ) (n + 1)) =
      fun x => (frestrictLe (π := fun _ : ℕ => ℝ) n x, x (n + 1)) := rfl

variable (P : (I : Finset ℕ) → Measure (I → ℝ))

noncomputable def gaussianExtensionJoint (n : ℕ) : Measure (RealPrefix n × ℝ) :=
  (P (Finset.Iic (n + 1))).map (realPrefixSplit n)

instance gaussianExtensionJoint_probability [∀ I, IsProbabilityMeasure (P I)] (n : ℕ) :
    IsProbabilityMeasure (gaussianExtensionJoint P n) :=
  Measure.isProbabilityMeasure_map (realPrefixSplit n).measurable.aemeasurable

noncomputable def gaussianExtensionKernel [∀ I, IsProbabilityMeasure (P I)] (n : ℕ) :
    Kernel (RealPrefix n) ℝ := (gaussianExtensionJoint P n).condKernel

instance gaussianExtensionKernel_markov [∀ I, IsProbabilityMeasure (P I)] (n : ℕ) :
    IsMarkovKernel (gaussianExtensionKernel P n) := by
  unfold gaussianExtensionKernel
  infer_instance

theorem gaussianExtensionJoint_fst (hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P) (n : ℕ) :
    (gaussianExtensionJoint P n).fst = P (Finset.Iic n) := by
  rw [Measure.fst, gaussianExtensionJoint, Measure.map_map measurable_fst (realPrefixSplit n).measurable,
    realPrefixSplit_fst]
  exact (hP (Finset.Iic (n + 1)) (Finset.Iic n)
    (Finset.Iic_subset_Iic.mpr (Nat.le_succ n))).symm

theorem gaussianExtension_disintegrate [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P) (n : ℕ) :
    P (Finset.Iic n) ⊗ₘ gaussianExtensionKernel P n = gaussianExtensionJoint P n := by
  rw [← gaussianExtensionJoint_fst P hP n]
  exact (gaussianExtensionJoint P n).disintegrate (gaussianExtensionJoint P n).condKernel

end TimeTraps.Probability
