module

public import TimeTraps.Spectral.CapacityRoot

@[expose] public section

/-!
The Robin phase equation has a unique positive scalar root when the interior
coefficients are positive and the two endpoint coefficients are nonnegative.
The endpoint zero cases are included. This analytical scalar result does not
identify the root with the physical Rayleigh minimum or a placement optimum;
those identifications require the physical phase and attainment arguments.
-/

namespace TimeTraps.Spectral

open scoped BigOperators

variable {ι : Type*}

noncomputable def robinPhaseCapacity (s : Finset ι) (a : ι → ℝ)
    (b0 bL k : ℝ) : ℝ :=
  Real.arctan (b0 / k) + Real.arctan (bL / k) + phaseCapacity s a k

theorem robinPhaseCapacity_continuousOn (s : Finset ι) (a : ι → ℝ) (b0 bL : ℝ) :
    ContinuousOn (robinPhaseCapacity s a b0 bL) (Set.Ioi 0) := by
  have h (b : ℝ) : ContinuousOn (fun k : ℝ => Real.arctan (b / k)) (Set.Ioi 0) :=
    Real.continuous_arctan.comp_continuousOn
      (continuousOn_const.div continuousOn_id (fun k hk => ne_of_gt hk))
  exact ((h b0).add (h bL)).add (phaseCapacity_continuousOn s a)

theorem phaseCapacity_le_robinPhaseCapacity (s : Finset ι) (a : ι → ℝ)
    {b0 bL k : ℝ} (hb0 : 0 ≤ b0) (hbL : 0 ≤ bL) (hk : 0 < k) :
    phaseCapacity s a k ≤ robinPhaseCapacity s a b0 bL k := by
  have h0 := Real.arctan_nonneg.mpr (div_nonneg hb0 hk.le)
  have hL := Real.arctan_nonneg.mpr (div_nonneg hbL hk.le)
  unfold robinPhaseCapacity
  linarith

theorem robinPhaseCapacity_lt_bound (s : Finset ι) (a : ι → ℝ) (b0 bL k : ℝ) :
    robinPhaseCapacity s a b0 bL k < ((s.card : ℝ) + 1) * Real.pi := by
  have hc : phaseCapacity s a k ≤ (s.card : ℝ) * Real.pi := by
    calc
      phaseCapacity s a k ≤ ∑ _j ∈ s, Real.pi := by
        apply Finset.sum_le_sum
        intro i _
        linarith [Real.arctan_lt_pi_div_two (a i / k)]
      _ = _ := by simp
  have h0 := Real.arctan_lt_pi_div_two (b0 / k)
  have hL := Real.arctan_lt_pi_div_two (bL / k)
  unfold robinPhaseCapacity
  nlinarith

theorem robinPhaseCapacity_strictAntiOn (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ j ∈ s, 0 < a j) {b0 bL : ℝ}
    (hb0 : 0 ≤ b0) (hbL : 0 ≤ bL) :
    StrictAntiOn (robinPhaseCapacity s a b0 bL) (Set.Ioi 0) := by
  intro k hk l hl hkl
  have h0 := Real.arctan_strictMono.monotone
    (div_le_div_of_nonneg_left hb0 hk hkl.le)
  have hL := Real.arctan_strictMono.monotone
    (div_le_div_of_nonneg_left hbL hk hkl.le)
  have hc := phaseCapacity_strictAntiOn s hs a ha hk hl hkl
  unfold robinPhaseCapacity
  linarith

theorem le_robin_capacity_root (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ j ∈ s, 0 < a j) {b0 bL L k r : ℝ}
    (hb0 : 0 ≤ b0) (hbL : 0 ≤ bL) (hL : 0 < L) (hk : 0 < k) (hr : 0 < r)
    (hroot : L * r = robinPhaseCapacity s a b0 bL r)
    (hbound : L * k ≤ robinPhaseCapacity s a b0 bL k) : k ≤ r := by
  by_contra h
  have hlt : r < k := lt_of_not_ge h
  have hc := robinPhaseCapacity_strictAntiOn s hs a ha hb0 hbL hr hk hlt
  have hlength := mul_lt_mul_of_pos_left hlt hL
  linarith

theorem lt_robin_capacity_root (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ j ∈ s, 0 < a j) {b0 bL L k r : ℝ}
    (hb0 : 0 ≤ b0) (hbL : 0 ≤ bL) (hL : 0 < L) (hk : 0 < k) (hr : 0 < r)
    (hroot : L * r = robinPhaseCapacity s a b0 bL r)
    (hbound : L * k < robinPhaseCapacity s a b0 bL k) : k < r := by
  have hle := le_robin_capacity_root s hs a ha hb0 hbL hL hk hr hroot hbound.le
  apply lt_of_le_of_ne hle
  intro he
  rw [he, ← hroot] at hbound
  exact (lt_irrefl _ hbound)

theorem robin_capacity_root_existsUnique (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ j ∈ s, 0 < a j) {b0 bL L : ℝ}
    (hb0 : 0 ≤ b0) (hbL : 0 ≤ bL) (hL : 0 < L) :
    ∃! k : ℝ, 0 < k ∧ L * k = robinPhaseCapacity s a b0 bL k := by
  obtain ⟨j, hj⟩ := hs
  have hs : s.Nonempty := ⟨j, hj⟩
  let lo := min (a j) (Real.pi / (4 * L))
  let upper := lo + (((s.card : ℝ) + 1) * Real.pi + 1) / L
  have hlo : 0 < lo := lt_min (ha j hj) (by positivity)
  have hstep : 0 < (((s.card : ℝ) + 1) * Real.pi + 1) / L := by positivity
  have horder : lo ≤ upper := by dsimp [upper]; linarith
  have hloSize : L * lo ≤ Real.pi / 4 := by
    have := (le_div_iff₀ (show 0 < 4 * L by positivity)).mp
      (min_le_right (a j) (Real.pi / (4 * L)))
    dsimp [lo]
    linarith
  have hloTerm : Real.pi / 2 ≤ 2 * Real.arctan (a j / lo) := by
    have hratio : 1 ≤ a j / lo := (le_div_iff₀ hlo).mpr
      (by simpa only [one_mul] using (show lo ≤ a j from min_le_left _ _))
    have := Real.arctan_strictMono.monotone hratio
    rw [Real.arctan_one] at this
    linarith
  have hloCap : Real.pi / 2 ≤ robinPhaseCapacity s a b0 bL lo := by
    apply hloTerm.trans
    apply le_trans ?_ (phaseCapacity_le_robinPhaseCapacity s a hb0 hbL hlo)
    exact Finset.single_le_sum
      (fun i hi => mul_nonneg (by norm_num)
        (Real.arctan_nonneg.mpr (div_nonneg (ha i hi).le hlo.le))) hj
  have hupperCap : robinPhaseCapacity s a b0 bL upper ≤ ((s.card : ℝ) + 1) * Real.pi :=
    (robinPhaseCapacity_lt_bound s a b0 bL upper).le
  have hupperSize : ((s.card : ℝ) + 1) * Real.pi < L * upper := by
    have hid : L * upper = L * lo + ((s.card : ℝ) + 1) * Real.pi + 1 := by
      dsimp [upper]
      field_simp
      ring
    rw [hid]
    have := mul_pos hL hlo
    linarith
  have hc : ContinuousOn (fun k => robinPhaseCapacity s a b0 bL k - L * k) (Set.Icc lo upper) :=
    ((robinPhaseCapacity_continuousOn s a b0 bL).mono
      (fun k hk => lt_of_lt_of_le hlo hk.1)).sub (continuousOn_const.mul continuousOn_id)
  have hloResidual : 0 ≤ robinPhaseCapacity s a b0 bL lo - L * lo := by linarith [Real.pi_pos]
  have hupperResidual : robinPhaseCapacity s a b0 bL upper - L * upper ≤ 0 := by linarith
  obtain ⟨k, hk, heq⟩ := intermediate_value_Icc' horder hc ⟨hupperResidual, hloResidual⟩
  have hkpos : 0 < k := lt_of_lt_of_le hlo hk.1
  have hkroot : L * k = robinPhaseCapacity s a b0 bL k := by linarith
  refine ⟨k, ⟨hkpos, hkroot⟩, ?_⟩
  intro r hr
  exact le_antisymm
    (le_robin_capacity_root s hs a ha hb0 hbL hL hr.1 hkpos hkroot hr.2.le)
    (le_robin_capacity_root s hs a ha hb0 hbL hL hkpos hr.1 hr.2 hkroot.le)

theorem robin_capacity_root_upper (s : Finset ι) (a : ι → ℝ) {b0 bL L k : ℝ}
    (hL : 0 < L) (hroot : L * k = robinPhaseCapacity s a b0 bL k) :
    k < (((s.card : ℝ) + 1) * Real.pi) / L := by
  apply (lt_div_iff₀ hL).mpr
  rw [mul_comm, hroot]
  exact robinPhaseCapacity_lt_bound s a b0 bL k

/-- The scalar Robin equation with the physical diffusion and reaction coefficients. -/
theorem robin_spectral_root_existsUnique (s : Finset ι) (hs : s.Nonempty)
    (κ : ι → ℝ) (hκ : ∀ j ∈ s, 0 < κ j) {D L β0 βL : ℝ}
    (hD : 0 < D) (hL : 0 < L) (hβ0 : 0 ≤ β0) (hβL : 0 ≤ βL) :
    ∃! k : ℝ, 0 < k ∧ L * k =
      Real.arctan (β0 / (D * k)) + Real.arctan (βL / (D * k)) +
        2 * ∑ j ∈ s, Real.arctan (κ j / (2 * D * k)) := by
  have hc : ∀ k, robinPhaseCapacity s (fun j => κ j / (2 * D)) (β0 / D) (βL / D) k =
      Real.arctan (β0 / (D * k)) + Real.arctan (βL / (D * k)) +
        2 * ∑ j ∈ s, Real.arctan (κ j / (2 * D * k)) := by
    intro k
    simp only [robinPhaseCapacity, phaseCapacity, div_div, Finset.mul_sum]
  simpa only [hc] using robin_capacity_root_existsUnique s hs (fun j => κ j / (2 * D))
    (fun j hj => div_pos (hκ j hj) (by positivity))
    (div_nonneg hβ0 hD.le) (div_nonneg hβL hD.le) hL

end TimeTraps.Spectral
