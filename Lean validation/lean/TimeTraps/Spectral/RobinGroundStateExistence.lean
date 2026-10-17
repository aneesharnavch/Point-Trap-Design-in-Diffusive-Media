module

public import TimeTraps.Spectral.RobinZeroExclusion
public import Mathlib.Topology.Order

@[expose] public section

/-!
An arbitrary ordered positive trap configuration with nonnegative endpoint
rates has a strictly positive sinusoidal state satisfying both Robin boundary
conditions. Compactness finds the first loss of positivity below pi / gap 0;
the right Robin residual changes sign before that loss. The spectral parameter
is obtained by the intermediate value theorem. Identification with the
independent Robin Rayleigh infimum is a separate theorem.
-/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem RobinShootingData.scaled_value_continuous (S : RobinShootingData n) :
    Continuous (fun p : ℝ × (Fin (n + 1) × ℝ) => S.value p.1 p.2.1 (S.gap p.2.1 * p.2.2)) := by
  have he : Continuous (fun p : Fin (n + 1) × (ℝ × ℝ) => S.value p.2.1 p.1 (S.gap p.1 * p.2.2)) := by
    apply continuous_prod_of_discrete_left.mpr
    intro e
    have hi : Continuous (fun p : ℝ × ℝ => (p.1, S.gap e * p.2)) :=
      continuous_fst.prodMk (continuous_const.mul continuous_snd)
    exact (S.value_continuous e).comp hi
  have hi : Continuous (fun p : ℝ × (Fin (n + 1) × ℝ) => (p.2.1, (p.1, p.2.2))) :=
    continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)
  have h := he.comp hi
  exact h

theorem RobinShootingData.first_zero_parameter (S : RobinShootingData n) :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / S.gap 0),
      (∀ k ∈ Ico (0 : ℝ) c, ∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 < S.value k e x) ∧
      (∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 ≤ S.value c e x) ∧
      S.value c (Fin.last n) (S.gap (Fin.last n)) = 0 := by
  let K : Set (Fin (n + 1) × ℝ) := univ ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hne : K.Nonempty := ⟨(0, 0), trivial, le_rfl, zero_le_one⟩
  have hB : 0 < Real.pi / S.gap 0 := div_pos Real.pi_pos (S.gap_pos 0)
  have h₀ : ∀ p ∈ K, 0 < S.value 0 p.1 (S.gap p.1 * p.2) := by
    intro p hp
    exact S.zero_parameter_positive p.1 (mul_nonneg (S.gap_pos p.1).le hp.2.1)
  have hBzero : ∃ p ∈ K, S.value (Real.pi / S.gap 0) p.1 (S.gap p.1 * p.2) ≤ 0 := by
    refine ⟨(0, 1), ⟨trivial, zero_le_one, le_rfl⟩, ?_⟩
    simp only [mul_one]
    rw [S.first_gap_negative]
    norm_num
  obtain ⟨c, hc, hbefore, hnonneg, p, hp, hzero⟩ :=
    compact_first_zero hK hne (u := fun k p => S.value k p.1 (S.gap p.1 * p.2))
      S.scaled_value_continuous hB h₀ hBzero
  have hparam (e : Fin (n + 1)) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (S.gap e)) :
      (e, x / S.gap e) ∈ K :=
    ⟨trivial, div_nonneg hx.1 (S.gap_pos e).le, (div_le_one (S.gap_pos e)).mpr hx.2⟩
  have hlocal : ∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 ≤ S.value c e x := by
    intro e x hx
    have h := hnonneg (e, x / S.gap e) (hparam e x hx)
    simpa only [mul_div_cancel₀ x (ne_of_gt (S.gap_pos e))] using h
  have hx : S.gap p.1 * p.2 ∈ Icc (0 : ℝ) (S.gap p.1) :=
    ⟨mul_nonneg (S.gap_pos p.1).le hp.2.1, by nlinarith [hp.2.2, S.gap_pos p.1]⟩
  have hend := S.zero_only_at_final_endpoint hlocal p.1 hx hzero
  refine ⟨c, hc, ?_, hlocal, ?_⟩
  · intro k hk e x hx
    have h := hbefore k hk (e, x / S.gap e) (hparam e x hx)
    simpa only [mul_div_cancel₀ x (ne_of_gt (S.gap_pos e))] using h
  · rw [hend.2, hend.1] at hzero
    exact hzero

theorem RobinShootingData.positive_robin_parameter (S : RobinShootingData n) (hn : 0 < n) :
    ∃ k ∈ Ioo (0 : ℝ) (Real.pi / S.gap 0),
      S.residual k = 0 ∧ ∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 < S.value k e x := by
  obtain ⟨c, hc, hbefore, hnonneg, hzero⟩ := S.first_zero_parameter
  have hR₀ := S.residual_zero_pos hn
  have hRc := S.residual_neg_at_zero hnonneg hzero
  obtain ⟨k, hk, hR⟩ := intermediate_value_Icc' hc.1.le S.residual_continuous.continuousOn
    (show (0 : ℝ) ∈ Icc (S.residual c) (S.residual 0) from ⟨hRc.le, hR₀.le⟩)
  have hkp : 0 < k := lt_of_le_of_ne hk.1 (by
    intro he
    rw [← he] at hR
    exact (ne_of_gt hR₀) hR)
  have hkc : k < c := lt_of_le_of_ne hk.2 (by
    intro he
    rw [he] at hR
    exact (ne_of_lt hRc) hR)
  exact ⟨k, ⟨hkp, hkc.trans_le hc.2⟩, hR, hbefore k ⟨hkp.le, hkc⟩⟩

end TimeTraps.Spectral
