module

public import TimeTraps.Analysis.CompactSpectralBasis
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Data.Set.Countable

@[expose] public section

/-! Compactness forces only finitely many eigenvectors, counting multiplicity,
to have eigenvalue above a fixed positive threshold.  Consequently the
constructed index is countable and the eigenvalues vanish along its cofinite
filter.  Finite-dimensional and zero-dimensional spaces are included. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

theorem compact_finite_separated_indices {X ι : Type*} [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K) (f : ι → X) (hf : ∀ i, f i ∈ K)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : Pairwise fun i j => ε ≤ dist (f i) (f j)) : Finite ι := by
  classical
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (ε / 3) (by positivity)
  have hc : ∀ i, ∃ c ∈ s, dist (f i) c < ε / 3 := by
    intro i
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using hcover (hf i)
  choose c hcs hcd using hc
  let _ := hs.to_subtype
  apply Finite.of_injective (fun i => (⟨c i, hcs i⟩ : s))
  intro i j hij
  by_contra hne
  have hcij : c i = c j := congrArg Subtype.val hij
  have hd := dist_triangle (f i) (c i) (f j)
  have hj := hcd j
  rw [← hcij, dist_comm (f j)] at hj
  have hl := hsep hne
  linarith [hcd i]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.eigenvalue_le_image_distance {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) {i j : CompactSpectralIndex T} (hij : i ≠ j) :
    i.1 ≤ dist (T (h.eigenbasis i)) (T (h.eigenbasis j)) := by
  have hi : inner ℝ (h.eigenbasis i)
      (T (h.eigenbasis i) - T (h.eigenbasis j)) = i.1 := by
    rw [inner_sub_right, h.eigenbasis_eigen, h.eigenbasis_eigen,
      inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq,
      h.eigenbasis.orthonormal.1 i, h.eigenbasis.orthonormal.2 hij]
    ring
  have hbound := abs_real_inner_le_norm (h.eigenbasis i)
    (T (h.eigenbasis i) - T (h.eigenbasis j))
  rw [hi, h.eigenbasis.orthonormal.1 i, one_mul,
    abs_of_pos (h.eigenbasis_positive i)] at hbound
  simpa only [dist_eq_norm] using hbound

theorem CompactPositiveInverse.finite_eigenvalues_ge {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) {ε : ℝ} (hε : 0 < ε) :
    {i : CompactSpectralIndex T | ε ≤ i.1}.Finite := by
  apply Set.finite_coe_iff.mp
  apply compact_finite_separated_indices
    (h.compact.isCompact_closure_image_closedBall 1)
    (fun i : {i : CompactSpectralIndex T | ε ≤ i.1} => T (h.eigenbasis i.val))
  · intro i
    apply subset_closure
    refine ⟨h.eigenbasis i.val, ?_, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right, h.eigenbasis.orthonormal.1, le_refl]
  · exact hε
  · intro i j hij
    exact i.property.trans (h.eigenvalue_le_image_distance
      (fun he => hij (Subtype.ext he)))

theorem CompactPositiveInverse.eigenvalues_tendsto_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) :
    Tendsto (fun i : CompactSpectralIndex T => i.1) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  rw [Filter.eventually_cofinite]
  simpa only [Real.dist_eq, sub_zero, abs_of_pos (h.eigenbasis_positive _),
    not_lt] using h.finite_eigenvalues_ge hε

theorem CompactPositiveInverse.countable_index {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) : Countable (CompactSpectralIndex T) := by
  apply Set.countable_univ_iff.mp
  have hc : (⋃ n : ℕ, {i : CompactSpectralIndex T | 1 / (n + 1 : ℝ) ≤ i.1}).Countable :=
    Set.countable_iUnion fun n => (h.finite_eigenvalues_ge (by positivity)).countable
  apply hc.mono
  intro i _
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (h.eigenbasis_positive i)
  exact Set.mem_iUnion.mpr ⟨n, hn.le⟩

end TimeTraps.Analysis
