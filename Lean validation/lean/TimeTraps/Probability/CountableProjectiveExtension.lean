module

public import TimeTraps.Probability.CountableProjectivePrefix

@[expose] public section

/-! A concrete probability measure extending any projective family of standard Borel
probability laws over finite subsets of the natural numbers. Successive
disintegrations and Ionescu--Tulcea supply the measure; all finite marginals
are proved from the original projective family. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Preorder

variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

variable (P : (I : Finset ℕ) → Measure (I → α)) [∀ I, IsProbabilityMeasure (P I)]

noncomputable def borelCountableExtension : Measure (ℕ → α) :=
  Kernel.traj (X := fun _ : ℕ => α) (borelExtensionKernel α P) 0 ∘ₘ P (Finset.Iic 0)

instance borelCountableExtension_probability : IsProbabilityMeasure (borelCountableExtension α P) := by
  unfold borelCountableExtension
  infer_instance

theorem borelCountableExtension_joint (n : ℕ) :
    (borelCountableExtension α P).map (frestrictLe (π := fun _ : ℕ => α) n) ⊗ₘ
      borelExtensionKernel α P n =
    (borelCountableExtension α P).map (fun x => (frestrictLe n x, x (n + 1))) := by
  rw [Measure.compProd_eq_comp_prod, borelCountableExtension,
    Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod, Kernel.map_apply _ (by fun_prop),
    Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)]

theorem borelCountableExtension_prefix
    (hP : IsProjectiveMeasureFamily (α := fun _ => α) P) (n : ℕ) :
    (borelCountableExtension α P).map (frestrictLe (π := fun _ : ℕ => α) n) = P (Finset.Iic n) := by
  induction n with
  | zero =>
    rw [borelCountableExtension, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  | succ n ih =>
    apply (borelPrefixSplit α n).map_measurableEquiv_injective
    rw [Measure.map_map (borelPrefixSplit α n).measurable (by fun_prop), borelPrefixSplit_restrict,
      ← borelCountableExtension_joint, ih, borelExtension_disintegrate α P hP n]
    rfl

theorem borelCountableExtension_isProjectiveLimit
    (hP : IsProjectiveMeasureFamily (α := fun _ => α) P) :
    IsProjectiveLimit (borelCountableExtension α P) P :=
  (isProjectiveLimit_nat_iff hP _).mpr (borelCountableExtension_prefix α P hP)

theorem borel_projective_probability_extension_exists_unique
    (hP : IsProjectiveMeasureFamily (α := fun _ => α) P) :
    ∃! μ : Measure (ℕ → α), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  refine ⟨borelCountableExtension α P,
    ⟨inferInstance, borelCountableExtension_isProjectiveLimit α P hP⟩, ?_⟩
  intro μ hμ
  exact hμ.2.unique (borelCountableExtension_isProjectiveLimit α P hP)

end TimeTraps.Probability
