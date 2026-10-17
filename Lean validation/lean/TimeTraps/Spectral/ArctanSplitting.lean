module

public import TimeTraps.Spectral.ArctanConcavity

@[expose] public section

/-! Strict phase improvement when one positive strength is split in two.
Concavity is proved through zero, so the endpoint used in Jensen is justified. -/

namespace TimeTraps.Spectral

open Set

theorem scaledArctan_zero (c : ℝ) : scaledArctan c 0 = 0 := by
  simp [scaledArctan]

theorem scaledArctan_strictConcaveOn_nonneg {c : ℝ} (hc : 0 < c) :
    StrictConcaveOn ℝ (Ici 0) (scaledArctan c) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici 0)
  · exact (Real.continuous_arctan.comp (continuous_id.div_const c)).continuousOn
  · intro t ht
    exact scaledArctan_deriv_two_neg hc (by simpa only [interior_Ici, mem_Ioi] using ht)

theorem scaledArctan_split_lt {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    scaledArctan c (a + b) < scaledArctan c a + scaledArctan c b := by
  have ht := add_pos ha hb
  have hw : a / (a + b) + b / (a + b) = 1 := by field_simp
  have hs := scaledArctan_strictConcaveOn_nonneg hc
  have htmem : a + b ∈ Ici (0 : ℝ) := by simpa only [mem_Ici] using ht.le
  have hzmem : (0 : ℝ) ∈ Ici 0 := by simp
  have h₁ := hs.2 htmem hzmem (ne_of_gt ht)
    (div_pos ha ht) (div_pos hb ht) hw
  have h₂ := hs.2 htmem hzmem (ne_of_gt ht)
    (div_pos hb ht) (div_pos ha ht) (by linarith : b / (a + b) + a / (a + b) = 1)
  simp only [smul_eq_mul, scaledArctan_zero, mul_zero, add_zero,
    div_mul_cancel₀ _ (ne_of_gt ht)] at h₁ h₂
  have he : a / (a + b) * scaledArctan c (a + b) +
      b / (a + b) * scaledArctan c (a + b) = scaledArctan c (a + b) := by
    rw [← add_mul, hw, one_mul]
  linarith

end TimeTraps.Spectral
