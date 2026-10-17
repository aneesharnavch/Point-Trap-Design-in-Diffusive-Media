module

public import TimeTraps.Spectral.RobinCapacity

@[expose] public section

/-!
The limiting phase equation when either or both Robin coefficients diverge.
Each selected endpoint contributes exactly pi/2; every unselected endpoint
retains its finite Robin coefficient. The limiting positive root is proved
to exist uniquely by an analytical crossing argument.
-/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

variable {ι : Type*}

noncomputable def dirichletEndpointPhase (b : ℝ) (d : Bool) (k : ℝ) : ℝ :=
  if d then Real.pi / 2 else Real.arctan (b / k)

theorem dirichletEndpointPhase_nonneg {b k : ℝ} (d : Bool)
    (hb : 0 ≤ b) (hk : 0 < k) : 0 ≤ dirichletEndpointPhase b d k := by
  cases d
  · exact Real.arctan_nonneg.mpr (div_nonneg hb hk.le)
  · exact (half_pos Real.pi_pos).le

theorem dirichletEndpointPhase_le (b k : ℝ) (d : Bool) :
    dirichletEndpointPhase b d k ≤ Real.pi / 2 := by
  cases d
  · exact (Real.arctan_lt_pi_div_two _).le
  · exact le_rfl

theorem arctan_le_dirichletEndpointPhase (b k : ℝ) (d : Bool) :
    Real.arctan (b / k) ≤ dirichletEndpointPhase b d k := by
  cases d
  · exact le_rfl
  · exact (Real.arctan_lt_pi_div_two _).le

theorem dirichletEndpointPhase_continuousOn (b : ℝ) (d : Bool) :
    ContinuousOn (dirichletEndpointPhase b d) (Ioi 0) := by
  cases d
  · exact Real.continuous_arctan.comp_continuousOn
      (continuousOn_const.div continuousOn_id (fun k hk => ne_of_gt hk))
  · exact continuousOn_const

theorem dirichletEndpointPhase_antitoneOn {b : ℝ} (hb : 0 ≤ b) (d : Bool) :
    AntitoneOn (dirichletEndpointPhase b d) (Ioi 0) := by
  intro k hk l _ hkl
  cases d
  · exact Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left hb hk hkl)
  · exact le_rfl

noncomputable def dirichletPhaseCapacity (s : Finset ι) (a : ι → ℝ)
    (b0 bL : ℝ) (left right : Bool) (k : ℝ) : ℝ :=
  dirichletEndpointPhase b0 left k + dirichletEndpointPhase bL right k + phaseCapacity s a k

theorem dirichletPhaseCapacity_continuousOn (s : Finset ι) (a : ι → ℝ)
    (b0 bL : ℝ) (left right : Bool) :
    ContinuousOn (dirichletPhaseCapacity s a b0 bL left right) (Ioi 0) :=
  ((dirichletEndpointPhase_continuousOn b0 left).add
    (dirichletEndpointPhase_continuousOn bL right)).add (phaseCapacity_continuousOn s a)

theorem robinPhaseCapacity_le_dirichletPhaseCapacity (s : Finset ι) (a : ι → ℝ)
    (b0 bL : ℝ) (left right : Bool) (k : ℝ) :
    robinPhaseCapacity s a b0 bL k ≤ dirichletPhaseCapacity s a b0 bL left right k := by
  have h0 := arctan_le_dirichletEndpointPhase b0 k left
  have hL := arctan_le_dirichletEndpointPhase bL k right
  unfold robinPhaseCapacity dirichletPhaseCapacity
  linarith

theorem dirichletPhaseCapacity_le_bound (s : Finset ι) (a : ι → ℝ)
    (b0 bL : ℝ) (left right : Bool) (k : ℝ) :
    dirichletPhaseCapacity s a b0 bL left right k ≤ ((s.card : ℝ) + 1) * Real.pi := by
  have hc : phaseCapacity s a k ≤ (s.card : ℝ) * Real.pi := by
    calc
      _ ≤ ∑ _j ∈ s, Real.pi := by
        apply Finset.sum_le_sum
        intro i _
        linarith [Real.arctan_lt_pi_div_two (a i / k)]
      _ = _ := by simp
  have h0 := dirichletEndpointPhase_le b0 k left
  have hL := dirichletEndpointPhase_le bL k right
  unfold dirichletPhaseCapacity
  nlinarith

theorem dirichletPhaseCapacity_strictAntiOn (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) {b0 bL : ℝ}
    (hb0 : 0 ≤ b0) (hbL : 0 ≤ bL) (left right : Bool) :
    StrictAntiOn (dirichletPhaseCapacity s a b0 bL left right) (Ioi 0) := by
  intro k hk l hl hkl
  have h0 := dirichletEndpointPhase_antitoneOn hb0 left hk hl hkl.le
  have hL := dirichletEndpointPhase_antitoneOn hbL right hk hl hkl.le
  have hc := phaseCapacity_strictAntiOn s hs a ha hk hl hkl
  unfold dirichletPhaseCapacity
  linarith

theorem le_dirichlet_capacity_root (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) {b0 bL L k r : ℝ}
    (hb0 : 0 ≤ b0) (hbL : 0 ≤ bL) (left right : Bool)
    (hL : 0 < L) (hk : 0 < k) (hr : 0 < r)
    (hroot : L * r = dirichletPhaseCapacity s a b0 bL left right r)
    (hbound : L * k ≤ dirichletPhaseCapacity s a b0 bL left right k) : k ≤ r := by
  by_contra h
  have hlt : r < k := lt_of_not_ge h
  have hc := dirichletPhaseCapacity_strictAntiOn s hs a ha hb0 hbL left right hr hk hlt
  have hlength := mul_lt_mul_of_pos_left hlt hL
  linarith

theorem dirichlet_capacity_root_existsUnique (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) {b0 bL L : ℝ}
    (hb0 : 0 ≤ b0) (hbL : 0 ≤ bL) (left right : Bool) (hL : 0 < L) :
    ∃! k : ℝ, 0 < k ∧ L * k = dirichletPhaseCapacity s a b0 bL left right k := by
  obtain ⟨lo, hlo, _⟩ := robin_capacity_root_existsUnique s hs a ha hb0 hbL hL
  let upper := lo + (((s.card : ℝ) + 1) * Real.pi + 1) / L
  have hstep : 0 < (((s.card : ℝ) + 1) * Real.pi + 1) / L := by positivity
  have horder : lo ≤ upper := by dsimp [upper]; linarith
  have hloCap : L * lo ≤ dirichletPhaseCapacity s a b0 bL left right lo := by
    rw [hlo.2]
    exact robinPhaseCapacity_le_dirichletPhaseCapacity s a b0 bL left right lo
  have hupperCap := dirichletPhaseCapacity_le_bound s a b0 bL left right upper
  have hupperSize : ((s.card : ℝ) + 1) * Real.pi < L * upper := by
    have hid : L * upper = L * lo + ((s.card : ℝ) + 1) * Real.pi + 1 := by
      dsimp [upper]
      field_simp
      ring
    rw [hid]
    have hp := mul_pos hL hlo.1
    linarith
  have hc : ContinuousOn
      (fun k => dirichletPhaseCapacity s a b0 bL left right k - L * k) (Icc lo upper) :=
    ((dirichletPhaseCapacity_continuousOn s a b0 bL left right).mono
      (fun k hk => lt_of_lt_of_le hlo.1 hk.1)).sub (continuousOn_const.mul continuousOn_id)
  obtain ⟨k, hk, he⟩ := intermediate_value_Icc' horder hc
    (show dirichletPhaseCapacity s a b0 bL left right upper - L * upper ≤ 0 ∧
      0 ≤ dirichletPhaseCapacity s a b0 bL left right lo - L * lo from
        ⟨by linarith, by linarith⟩)
  have hkpos : 0 < k := hlo.1.trans_le hk.1
  have hroot : L * k = dirichletPhaseCapacity s a b0 bL left right k := by linarith
  refine ⟨k, ⟨hkpos, hroot⟩, ?_⟩
  intro r hr
  exact le_antisymm
    (le_dirichlet_capacity_root s hs a ha hb0 hbL left right hL hr.1 hkpos hroot hr.2.le)
    (le_dirichlet_capacity_root s hs a ha hb0 hbL left right hL hkpos hr.1 hr.2 hroot.le)

end TimeTraps.Spectral
