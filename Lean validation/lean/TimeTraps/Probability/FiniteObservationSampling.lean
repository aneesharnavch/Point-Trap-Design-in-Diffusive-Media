module

public import TimeTraps.Probability.ProjectiveObservationPullback
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! A finite observation set is included in a countable sampling sequence
without changing or duplicating any of its retained coordinates. -/

namespace TimeTraps.Probability

open MeasureTheory

variable {β : Type*} [DecidableEq β]

noncomputable def finiteObservationSampling (b₀ : β) (I : Finset β) (n : ℕ) : β :=
  if hn : n < I.card then ((I.equivFin).symm ⟨n, hn⟩).val else b₀

noncomputable def finiteObservationSamplingIndex (I : Finset β) (i : I) :
    ↥(Finset.range I.card) := ⟨(I.equivFin i).val, Finset.mem_range.mpr (I.equivFin i).isLt⟩

omit [DecidableEq β] in
theorem finiteObservationSampling_index (b₀ : β) (I : Finset β) (i : I) :
    finiteObservationSampling b₀ I (finiteObservationSamplingIndex I i).val = i.val := by
  unfold finiteObservationSampling finiteObservationSamplingIndex
  split_ifs with hn
  · change ((I.equivFin).symm (I.equivFin i)).val = i.val
    rw [Equiv.symm_apply_apply]
  · exact (hn (I.equivFin i).isLt).elim

theorem finiteObservationSampling_range (b₀ : β) (I : Finset β) :
    (Finset.range I.card).image (finiteObservationSampling b₀ I) = I := by
  ext b
  constructor
  · intro hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    have hn' := Finset.mem_range.mp hn
    simp only [finiteObservationSampling, dif_pos hn']
    exact ((I.equivFin).symm ⟨n, hn'⟩).property
  · intro hb
    let i : I := ⟨b, hb⟩
    exact Finset.mem_image.mpr ⟨(finiteObservationSamplingIndex I i).val,
      (finiteObservationSamplingIndex I i).property, finiteObservationSampling_index b₀ I i⟩

end TimeTraps.Probability
