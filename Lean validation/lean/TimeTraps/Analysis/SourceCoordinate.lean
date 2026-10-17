module

public import TimeTraps.Analysis.EdgeReconstruction
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Analysis.Calculus.Deriv.Inverse

@[expose] public section

/-!
The normalized source coordinate on a physical interval. Only continuity and
strict positivity of the source are assumed. Its inverse is first constructed
as an order isomorphism of closed intervals; constant extension outside the
unit interval supplies an ordinary real-valued function for interior calculus.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

structure SourceInterval where
  left : ℝ
  right : ℝ
  increasing : left < right
  density : ℝ → ℝ
  continuous : ContinuousOn density (Icc left right)
  positive : ∀ x ∈ Icc left right, 0 < density x

noncomputable def SourceInterval.mass (P : SourceInterval) : ℝ :=
  ∫ x in P.left..P.right, P.density x

noncomputable def SourceInterval.coordinate (P : SourceInterval) (x : ℝ) : ℝ :=
  (∫ t in P.left..x, P.density t) / P.mass

theorem SourceInterval.mass_pos (P : SourceInterval) : 0 < P.mass := by
  apply intervalIntegral.integral_pos P.increasing P.continuous
  · intro x hx
    exact (P.positive x ⟨hx.1.le, hx.2⟩).le
  · exact ⟨P.left, ⟨le_rfl, P.increasing.le⟩, P.positive P.left ⟨le_rfl, P.increasing.le⟩⟩

theorem SourceInterval.coordinate_left (P : SourceInterval) : P.coordinate P.left = 0 := by
  simp [SourceInterval.coordinate]

theorem SourceInterval.coordinate_right (P : SourceInterval) : P.coordinate P.right = 1 := by
  exact div_self (ne_of_gt P.mass_pos)

theorem SourceInterval.coordinate_continuous (P : SourceInterval) :
    ContinuousOn P.coordinate (Icc P.left P.right) :=
  (integral_primitive_continuousOn P.increasing.le P.continuous).div_const P.mass

theorem SourceInterval.coordinate_derivative (P : SourceInterval) {x : ℝ}
    (hx : x ∈ Ioo P.left P.right) :
    HasDerivAt P.coordinate (P.density x / P.mass) x :=
  (integral_primitive_hasDerivAt P.continuous hx).div_const P.mass

theorem SourceInterval.coordinate_strictMono (P : SourceInterval) :
    StrictMonoOn P.coordinate (Icc P.left P.right) := by
  intro x hx y hy hxy
  exact div_lt_div_of_pos_right
    (integral_primitive_strictMonoOn P.increasing.le P.continuous
      (fun t ht => P.positive t (Ioo_subset_Icc_self ht)) hx hy hxy) P.mass_pos

theorem SourceInterval.coordinate_image (P : SourceInterval) :
    P.coordinate '' Icc P.left P.right = Icc 0 1 := by
  simpa only [P.coordinate_left, P.coordinate_right] using
    P.coordinate_continuous.image_Icc_of_monotoneOn P.increasing.le
      P.coordinate_strictMono.monotoneOn

theorem SourceInterval.coordinate_mem (P : SourceInterval) {x : ℝ}
    (hx : x ∈ Icc P.left P.right) : P.coordinate x ∈ Icc 0 1 := by
  rw [← P.coordinate_image]
  exact mem_image_of_mem _ hx

noncomputable def SourceInterval.orderIso (P : SourceInterval) :
    Icc P.left P.right ≃o Icc (0 : ℝ) 1 :=
  (P.coordinate_strictMono.orderIso P.coordinate (Icc P.left P.right)).trans
    (OrderIso.setCongr _ _ P.coordinate_image)

theorem SourceInterval.orderIso_apply (P : SourceInterval) (x : Icc P.left P.right) :
    (P.orderIso x : ℝ) = P.coordinate x := rfl

noncomputable def SourceInterval.inverse (P : SourceInterval) (z : ℝ) : ℝ :=
  P.orderIso.symm (projIcc 0 1 zero_le_one z)

theorem SourceInterval.inverse_mem (P : SourceInterval) (z : ℝ) :
    P.inverse z ∈ Icc P.left P.right := (P.orderIso.symm (projIcc 0 1 zero_le_one z)).property

theorem SourceInterval.inverse_continuous (P : SourceInterval) : Continuous P.inverse :=
  continuous_subtype_val.comp
    (P.orderIso.symm.toHomeomorph.continuous.comp continuous_projIcc)

theorem SourceInterval.coordinate_inverse (P : SourceInterval) {z : ℝ} (hz : z ∈ Icc 0 1) :
    P.coordinate (P.inverse z) = z := by
  have h := congrArg (fun x : Icc (0 : ℝ) 1 => (x : ℝ))
    (P.orderIso.apply_symm_apply (projIcc 0 1 zero_le_one z))
  simpa only [SourceInterval.inverse, P.orderIso_apply, projIcc_of_mem zero_le_one hz] using h

theorem SourceInterval.inverse_coordinate (P : SourceInterval) {x : ℝ}
    (hx : x ∈ Icc P.left P.right) : P.inverse (P.coordinate x) = x := by
  apply P.coordinate_strictMono.injOn (P.inverse_mem _) hx
  exact P.coordinate_inverse (P.coordinate_mem hx)

theorem SourceInterval.inverse_zero (P : SourceInterval) : P.inverse 0 = P.left := by
  rw [← P.coordinate_left]
  exact P.inverse_coordinate ⟨le_rfl, P.increasing.le⟩

theorem SourceInterval.inverse_one (P : SourceInterval) : P.inverse 1 = P.right := by
  rw [← P.coordinate_right]
  exact P.inverse_coordinate ⟨P.increasing.le, le_rfl⟩

theorem SourceInterval.inverse_strictMono (P : SourceInterval) :
    StrictMonoOn P.inverse (Icc 0 1) := by
  intro z hz w hw hzw
  apply (P.coordinate_strictMono.lt_iff_lt (P.inverse_mem z) (P.inverse_mem w)).mp
  simpa only [P.coordinate_inverse hz, P.coordinate_inverse hw] using hzw

theorem SourceInterval.inverse_image (P : SourceInterval) :
    P.inverse '' Icc 0 1 = Icc P.left P.right := by
  simpa only [P.inverse_zero, P.inverse_one] using
    P.inverse_continuous.continuousOn.image_Icc_of_monotoneOn zero_le_one
      P.inverse_strictMono.monotoneOn

theorem SourceInterval.sourcePrimitive_eq (P : SourceInterval) (x : ℝ) :
    sourcePrimitive P.density P.left x = P.mass * P.coordinate x := by
  unfold SourceInterval.coordinate sourcePrimitive
  field_simp [ne_of_gt P.mass_pos]

theorem SourceInterval.mass_fraction (P : SourceInterval) {x y : ℝ}
    (hx : x ∈ Icc P.left P.right) (hy : y ∈ Icc P.left P.right) (hxy : x ≤ y) :
    (∫ t in x..y, P.density t) = P.mass * (P.coordinate y - P.coordinate x) := by
  have hi₁ := (P.continuous.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc
    (μ := volume) hx.1
  have hi₂ := (P.continuous.mono (Icc_subset_Icc hx.1 hy.2)).intervalIntegrable_of_Icc
    (μ := volume) hxy
  have hs := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  change sourcePrimitive P.density P.left x + (∫ t in x..y, P.density t) =
    sourcePrimitive P.density P.left y at hs
  rw [P.sourcePrimitive_eq x, P.sourcePrimitive_eq y] at hs
  linarith

theorem SourceInterval.coordinate_interior (P : SourceInterval) {x : ℝ}
    (hx : x ∈ Ioo P.left P.right) : P.coordinate x ∈ Ioo 0 1 := by
  constructor
  · simpa only [P.coordinate_left] using P.coordinate_strictMono
      ⟨le_rfl, P.increasing.le⟩ (Ioo_subset_Icc_self hx) hx.1
  · simpa only [P.coordinate_right] using P.coordinate_strictMono
      (Ioo_subset_Icc_self hx) ⟨P.increasing.le, le_rfl⟩ hx.2

theorem SourceInterval.inverse_interior (P : SourceInterval) {z : ℝ}
    (hz : z ∈ Ioo 0 1) : P.inverse z ∈ Ioo P.left P.right := by
  constructor
  · simpa only [P.inverse_zero] using P.inverse_strictMono
      ⟨le_rfl, zero_le_one⟩ (Ioo_subset_Icc_self hz) hz.1
  · simpa only [P.inverse_one] using P.inverse_strictMono
      (Ioo_subset_Icc_self hz) ⟨zero_le_one, le_rfl⟩ hz.2

/-- The inverse Jacobian requires no derivative of the source density. -/
theorem SourceInterval.inverse_derivative (P : SourceInterval) {z : ℝ}
    (hz : z ∈ Ioo 0 1) :
    HasDerivAt P.inverse (P.mass / P.density (P.inverse z)) z := by
  have hn : P.density (P.inverse z) / P.mass ≠ 0 :=
    ne_of_gt (div_pos (P.positive _ (P.inverse_mem z)) P.mass_pos)
  have hi : ∀ᶠ w in 𝓝 z, P.coordinate (P.inverse w) = w := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
    exact P.coordinate_inverse (Ioo_subset_Icc_self hw)
  simpa only [inv_div] using HasDerivAt.of_local_left_inverse
    P.inverse_continuous.continuousAt (P.coordinate_derivative (P.inverse_interior hz)) hn hi

end TimeTraps.Analysis
