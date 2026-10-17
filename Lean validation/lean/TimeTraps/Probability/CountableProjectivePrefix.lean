module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Tactic

@[expose] public section

/-! Successive disintegration of a projective family of standard Borel probability
laws. These are actual Markov kernels, ready for Ionescu--Tulcea extension;
no stochastic process or extension measure is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

variable (α : Type*) [MeasurableSpace α]

abbrev BorelPrefix (n : ℕ) := (i : Finset.Iic n) → α

set_option backward.isDefEq.respectTransparency false in
def borelPrefixSplit (n : ℕ) : BorelPrefix α (n + 1) ≃ᵐ BorelPrefix α n × α where
  toFun x := (frestrictLe₂ (π := fun _ : ℕ => α) (Nat.le_succ n) x,
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
    change Measurable (fun x : BorelPrefix α (n + 1) =>
      (frestrictLe₂ (π := fun _ : ℕ => α) (Nat.le_succ n) x,
        x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩))
    exact (measurable_frestrictLe₂ (X := fun _ : ℕ => α) (Nat.le_succ n)).prodMk
      (measurable_pi_apply (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1)))
  measurable_invFun := by
    change Measurable (fun z : BorelPrefix α n × α => fun i : Finset.Iic (n + 1) =>
      if h : i.val ≤ n then z.1 ⟨i.val, Finset.mem_Iic.mpr h⟩ else z.2)
    refine measurable_pi_lambda _ fun i => ?_
    by_cases hi : i.val ≤ n
    · simpa only [hi, dite_true, Function.comp_def] using
        (measurable_pi_apply (⟨i.val, Finset.mem_Iic.mpr hi⟩ : Finset.Iic n)).comp measurable_fst
    · simpa only [hi, dite_false] using measurable_snd

theorem borelPrefixSplit_fst (n : ℕ) :
    Prod.fst ∘ borelPrefixSplit α n = frestrictLe₂ (π := fun _ : ℕ => α) (Nat.le_succ n) := rfl

theorem borelPrefixSplit_restrict (n : ℕ) :
    borelPrefixSplit α n ∘ (frestrictLe (π := fun _ : ℕ => α) (n + 1)) =
      fun x => (frestrictLe (π := fun _ : ℕ => α) n x, x (n + 1)) := rfl

variable [StandardBorelSpace α] [Nonempty α]

variable (P : (I : Finset ℕ) → Measure (I → α))

noncomputable def borelExtensionJoint (n : ℕ) : Measure (BorelPrefix α n × α) :=
  (P (Finset.Iic (n + 1))).map (borelPrefixSplit α n)

instance borelExtensionJoint_probability [∀ I, IsProbabilityMeasure (P I)] (n : ℕ) :
    IsProbabilityMeasure (borelExtensionJoint α P n) :=
  Measure.isProbabilityMeasure_map (borelPrefixSplit α n).measurable.aemeasurable

noncomputable def borelExtensionKernel [∀ I, IsProbabilityMeasure (P I)] (n : ℕ) :
    Kernel (BorelPrefix α n) α := (borelExtensionJoint α P n).condKernel

instance borelExtensionKernel_markov [∀ I, IsProbabilityMeasure (P I)] (n : ℕ) :
    IsMarkovKernel (borelExtensionKernel α P n) := by
  unfold borelExtensionKernel
  infer_instance

omit [StandardBorelSpace α] [Nonempty α] in
theorem borelExtensionJoint_fst (hP : IsProjectiveMeasureFamily (α := fun _ => α) P) (n : ℕ) :
    (borelExtensionJoint α P n).fst = P (Finset.Iic n) := by
  rw [Measure.fst, borelExtensionJoint, Measure.map_map measurable_fst (borelPrefixSplit α n).measurable,
    borelPrefixSplit_fst]
  exact (hP (Finset.Iic (n + 1)) (Finset.Iic n)
    (Finset.Iic_subset_Iic.mpr (Nat.le_succ n))).symm

theorem borelExtension_disintegrate [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ => α) P) (n : ℕ) :
    P (Finset.Iic n) ⊗ₘ borelExtensionKernel α P n = borelExtensionJoint α P n := by
  rw [← borelExtensionJoint_fst α P hP n]
  exact (borelExtensionJoint α P n).disintegrate (borelExtensionJoint α P n).condKernel

end TimeTraps.Probability
