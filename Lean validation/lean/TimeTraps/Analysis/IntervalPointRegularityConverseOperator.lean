module

public import TimeTraps.Analysis.IntervalPointRegularityConverseGreen
public import TimeTraps.Analysis.IntervalPointRegularityConverseGluing
public import TimeTraps.Analysis.IntervalPointRegularityPhysical

@[expose] public section

/-! Exact strong-domain characterization on any contact-containing
partition. Global H1 membership is derived from the closed-piece data;
the input state is only an L2 equivalence class. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {P : UnitPointProblem ι} {n : ℕ}

theorem UnitPointPartition.weak_of_slopes (Q : UnitPointPartition P n)
    (f : UnitIntervalL2) {U : ℝ → ℝ} (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) (ht : UnitPointTransmission Q U j) :
    ∀ ψ : ℝ → ℝ, IntervalEnergy ψ 0 1 →
      unitPointForm P.diffusivity P.strength P.site U ψ = ∫ x in (0 : ℝ)..1, f x * ψ x :=
  Q.weak_of_piecewise f (Q.energy_of_slopes hj) j hj ht

theorem UnitPointPartition.operator_graph_of_piecewise (Q : UnitPointPartition P n)
    (u f : UnitIntervalL2) (U : ℝ → ℝ)
    (hu : u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] U)
    (j : Fin (n + 1) → ℝ → ℝ)
    (hj : ∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
      (Q.point e.castSucc) (Q.point e.succ)) (ht : UnitPointTransmission Q U j) :
    (u, f) ∈ P.operator.graph := by
  have hU := Q.energy_of_slopes hj
  have he : u = (ofEnergy hU zero_lt_one).state :=
    Lp.ext (hu.trans (ofEnergy_spec hU zero_lt_one).1.symm)
  rw [he]
  exact (P.operator_graph_iff_physical f hU).mpr (Q.weak_of_slopes f j hj ht)

theorem UnitPointPartition.operator_graph_iff_piecewise (Q : UnitPointPartition P n)
    (u f : UnitIntervalL2) :
    (u, f) ∈ P.operator.graph ↔
      ∃ (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ UnitPointTransmission Q U j := by
  constructor
  · intro hg
    obtain ⟨U, j, _, hu, hj, ht⟩ := Q.operator_graph_piecewise_regularity u f hg
    exact ⟨U, j, hu, hj, ht⟩
  · rintro ⟨U, j, hu, hj, ht⟩
    exact Q.operator_graph_of_piecewise u f U hu j hj ht

theorem UnitPointPartition.operator_domain_iff_piecewise (Q : UnitPointPartition P n)
    (u : UnitIntervalL2) :
    u ∈ P.operator.domain ↔
      ∃ (f : UnitIntervalL2) (U : ℝ → ℝ) (j : Fin (n + 1) → ℝ → ℝ),
        u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] U ∧
        (∀ e, IntervalSlopeRegularity U (j e) (fun x => -f x / P.diffusivity)
          (Q.point e.castSucc) (Q.point e.succ)) ∧ UnitPointTransmission Q U j := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [Q.operator_graph_iff_piecewise]

end TimeTraps.Analysis
