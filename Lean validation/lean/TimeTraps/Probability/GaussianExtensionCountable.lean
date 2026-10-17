module

public import TimeTraps.Probability.GaussianExtensionPrefix

@[expose] public section

/-! A concrete probability measure extending any projective family of real
probability laws over finite subsets of the natural numbers. Successive
disintegrations and Ionescu--Tulcea supply the measure; all finite marginals
are proved from the original projective family. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Preorder

variable (P : (I : Finset ℕ) → Measure (I → ℝ)) [∀ I, IsProbabilityMeasure (P I)]

noncomputable def gaussianCountableExtension : Measure (ℕ → ℝ) :=
  Kernel.traj (X := fun _ : ℕ => ℝ) (gaussianExtensionKernel P) 0 ∘ₘ P (Finset.Iic 0)

instance gaussianCountableExtension_probability : IsProbabilityMeasure (gaussianCountableExtension P) := by
  unfold gaussianCountableExtension
  infer_instance

theorem gaussianCountableExtension_joint (n : ℕ) :
    (gaussianCountableExtension P).map (frestrictLe (π := fun _ : ℕ => ℝ) n) ⊗ₘ
      gaussianExtensionKernel P n =
    (gaussianCountableExtension P).map (fun x => (frestrictLe n x, x (n + 1))) := by
  rw [Measure.compProd_eq_comp_prod, gaussianCountableExtension,
    Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod, Kernel.map_apply _ (by fun_prop),
    Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)]

theorem gaussianCountableExtension_prefix
    (hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P) (n : ℕ) :
    (gaussianCountableExtension P).map (frestrictLe (π := fun _ : ℕ => ℝ) n) = P (Finset.Iic n) := by
  induction n with
  | zero =>
    rw [gaussianCountableExtension, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  | succ n ih =>
    apply (realPrefixSplit n).map_measurableEquiv_injective
    rw [Measure.map_map (realPrefixSplit n).measurable (by fun_prop), realPrefixSplit_restrict,
      ← gaussianCountableExtension_joint, ih, gaussianExtension_disintegrate P hP n]
    rfl

theorem gaussianCountableExtension_isProjectiveLimit
    (hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P) :
    IsProjectiveLimit (gaussianCountableExtension P) P :=
  (isProjectiveLimit_nat_iff hP _).mpr (gaussianCountableExtension_prefix P hP)

theorem real_projective_probability_extension_exists_unique
    (hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P) :
    ∃! μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  refine ⟨gaussianCountableExtension P,
    ⟨inferInstance, gaussianCountableExtension_isProjectiveLimit P hP⟩, ?_⟩
  intro μ hμ
  exact hμ.2.unique (gaussianCountableExtension_isProjectiveLimit P hP)

end TimeTraps.Probability
