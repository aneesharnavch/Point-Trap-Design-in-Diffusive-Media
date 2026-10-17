module

public import TimeTraps.Analysis.SignedIntervalPointStrongDomain

@[expose] public section

/-! The genuine empty-contact interval operator on [0,L]. Its one-cell
strong domain consists of actual AC/L2 states and slopes, with zero
endpoint slope traces. Identification with the reflected evolution is
a separate bridge; no spectral definition of Sobolev regularity is used. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

def reflectedNeumannProblem (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) :
    SignedIntervalPointProblem (Fin 0) 0 L where
  interval_pos := hL
  diffusivity := D
  diffusivity_pos := hD
  strength := Fin.elim0
  site := Fin.elim0
  site_mem i := Fin.elim0 i

def reflectedNeumannPartition (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) :
    SignedIntervalPointPartition (reflectedNeumannProblem L hL D hD) 0 where
  point i := if i = 0 then 0 else L
  strictMono := by
    intro i j hij
    have hi : i = 0 := by apply Fin.ext; change i.val = 0; omega
    have hj : j = 1 := by apply Fin.ext; change j.val = 1; omega
    subst i
    subst j
    simpa using hL
  left_eq := by simp
  right_eq := by simp
  contactNode := Fin.elim0
  contact_eq i := Fin.elim0 i

theorem reflectedNeumannPartition_nodeStrength (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (i : Fin 2) : (reflectedNeumannPartition L hL D hD).nodeStrength i = 0 := by
  simp [SignedIntervalPointPartition.nodeStrength]

theorem reflectedNeumann_operator_graph_iff (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (u f : IntervalSobolevL2 0 L) :
    (u, f) ∈ (reflectedNeumannProblem L hL D hD).operator.graph ↔
      ∃ U j : ℝ → ℝ, u =ᵐ[volume.restrict (Ioo 0 L)] U ∧
        IntervalSlopeRegularity U j (fun x => -f x / D) 0 L ∧ j 0 = 0 ∧ j L = 0 := by
  rw [(reflectedNeumannPartition L hL D hD).operator_graph_iff_piecewise]
  constructor
  · rintro ⟨U, j, hu, hj, ht⟩
    refine ⟨U, j 0, hu, ?_, ?_, ?_⟩
    · simpa [reflectedNeumannPartition, reflectedNeumannProblem] using hj 0
    · exact ht.left_neumann (reflectedNeumannPartition_nodeStrength L hL D hD 0)
    · simpa only [Fin.last_zero] using
        ht.right_neumann (reflectedNeumannPartition_nodeStrength L hL D hD (Fin.last 1))
  · rintro ⟨U, j, hu, hj, hleft, hright⟩
    refine ⟨U, fun _ => j, hu, ?_, ?_⟩
    · intro e
      have he : e = 0 := Fin.eq_zero e
      subst e
      simpa [reflectedNeumannPartition, reflectedNeumannProblem] using hj
    · constructor
      · simp only [reflectedNeumannPartition_nodeStrength, hleft, mul_zero, zero_mul]
      · simp only [reflectedNeumannPartition_nodeStrength, hright, mul_zero, neg_zero, zero_mul]
      · intro i
        exact Fin.elim0 i

theorem reflectedNeumann_operator_domain_iff (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (u : IntervalSobolevL2 0 L) :
    u ∈ (reflectedNeumannProblem L hL D hD).operator.domain ↔
      ∃ (f : IntervalSobolevL2 0 L) (U j : ℝ → ℝ), u =ᵐ[volume.restrict (Ioo 0 L)] U ∧
        IntervalSlopeRegularity U j (fun x => -f x / D) 0 L ∧ j 0 = 0 ∧ j L = 0 := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [reflectedNeumann_operator_graph_iff]

end TimeTraps.Probability

end
