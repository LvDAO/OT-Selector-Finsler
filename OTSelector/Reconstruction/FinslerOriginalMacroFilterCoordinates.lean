import OTSelector.Reconstruction.FinslerConcreteUpperOriginalMicrocellMacroIndices

/-! Affine unit-cube support supplies the actual macrobox bounds for the literal
original coordinate image. Filtering microcells preserves its entire trace. -/

open Set Function Module BoxIntegral
open scoped Classical

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

variable {q : ℕ}

/-- An original label with open unit-cube coordinates has every original basis
coordinate strictly inside the actual radius. -/
theorem basis_coordinates_bounds_of_labelCubeCoordinates_mem_unitCubeSet
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (basis : Basis (Fin q) ℝ W) {R : ℝ} (hR : 0 < R) {w : W}
    (hunit : labelCubeCoordinates basis R w ∈ unitCubeSet q) :
    ∀ l, -R < basis.equivFun w l ∧ basis.equivFun w l < R := by
  intro l
  have hl := hunit l (mem_univ l)
  change 0 < (basis.equivFun w l + R) / (2 * R) ∧
    (basis.equivFun w l + R) / (2 * R) < 1 at hl
  have hside : 0 < 2 * R := by positivity
  have hlo := (div_pos_iff_of_pos_right hside).mp hl.1
  have hhi := (div_lt_iff₀ hside).mp hl.2
  constructor <;> linarith

/-- Open unit-cube support of the original labels places every microcell
meeting their literal coordinate image in the actual macro-grid leaf range. -/
theorem originalMeetingMicrocells_labelImage_subset_macro_range
    {Z W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (basis : Basis (Fin q) ℝ W) (root : Z → W)
    {R n : ℕ} [NeZero n] (hR : 0 < R) (L : Set Z)
    (hunit : ∀ z ∈ L, labelCubeCoordinates basis (R : ℝ) (root z) ∈ unitCubeSet q)
    (cells : Finset (Fin q → ℤ)) :
    originalMeetingMicrocells n ((basis.equivFunL ∘ root) '' L) cells ⊆
      Finset.univ.image (originalMacroMicroIndex (q := q) R n) := by
  apply originalMeetingMicrocells_subset_macro_range
  rintro x ⟨z, hz, rfl⟩
  exact basis_coordinates_bounds_of_labelCubeCoordinates_mem_unitCubeSet basis
    (Nat.cast_pos.mpr hR) (hunit z hz)

/-- Membership in the microcell union is unchanged at every point of the
literal retained set. This is a pointwise form of the trace identity. -/
theorem originalMeetingMicrocells_mem_iUnion_iff
    (n : ℕ) [NeZero n] (s : Set (Fin q → ℝ)) (cells : Finset (Fin q → ℤ))
    {x : Fin q → ℝ} (hxs : x ∈ s) :
    x ∈ (⋃ ν ∈ originalMeetingMicrocells n s cells,
      (unitPartition.box n ν : Set (Fin q → ℝ))) ↔
    x ∈ (⋃ ν ∈ cells, (unitPartition.box n ν : Set (Fin q → ℝ))) := by
  have htrace := Set.ext_iff.mp (originalMeetingMicrocells_trace n s cells) x
  simpa only [Set.mem_inter_iff, hxs, true_and] using htrace

/-- An arbitrary original endpoint retains exactly the same microcell-union
membership after filtering against the literal coordinate image. -/
theorem originalMeetingMicrocells_image_mem_iUnion_iff
    {Z : Type*} (n : ℕ) [NeZero n] (coord : Z → Fin q → ℝ)
    (L : Set Z) (cells : Finset (Fin q → ℤ)) {z : Z} (hz : z ∈ L) :
    coord z ∈ (⋃ ν ∈ originalMeetingMicrocells n (coord '' L) cells,
      (unitPartition.box n ν : Set (Fin q → ℝ))) ↔
    coord z ∈ (⋃ ν ∈ cells, (unitPartition.box n ν : Set (Fin q → ℝ))) := by
  exact originalMeetingMicrocells_mem_iUnion_iff n (coord '' L) cells
    (Set.mem_image_of_mem coord hz)

/-- A cover of the original endpoints on any additional retained set remains
the same cover after filtering; no original endpoint is removed. -/
theorem originalMeetingMicrocells_image_covers_inter
    {Z : Type*} (n : ℕ) [NeZero n] (coord : Z → Fin q → ℝ)
    (L G : Set Z) (cells : Finset (Fin q → ℤ))
    (hcover : ∀ z ∈ L ∩ G,
      coord z ∈ (⋃ ν ∈ cells, (unitPartition.box n ν : Set (Fin q → ℝ)))) :
    ∀ z ∈ L ∩ G,
      coord z ∈ (⋃ ν ∈ originalMeetingMicrocells n (coord '' L) cells,
        (unitPartition.box n ν : Set (Fin q → ℝ))) := by
  intro z hz
  exact (originalMeetingMicrocells_image_mem_iUnion_iff n coord L cells hz.1).mpr
    (hcover z hz)

end OTSelector.Reconstruction
