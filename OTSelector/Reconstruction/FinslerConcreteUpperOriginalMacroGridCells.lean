import OTSelector.Probability.HaarAffineUnitPartition
import OTSelector.Probability.MarkedBlockValueIntegral
import OTSelector.Analysis.Normed.BallCubeEmbedding
import OTSelector.Reconstruction.MarkedStationaryValueLegalNestedBlocks

/-! The original Haar microboxes and the actual floor-grid leaves agree away
from the null coordinate faces. The integer macro radius keeps the original
microscopic side length literal. -/
open Set Function MeasureTheory ProbabilityTheory Module
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- Every coordinate grid face has zero original Haar mass, simultaneously
over the countable family of literal half-open boxes. -/
theorem ae_original_grid_coordinates_nonintegral
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] :
    ∀ᵐ x ∂μ, ∀ l : Fin q, ∀ z : ℤ, (n : ℝ) * e x l ≠ (z : ℝ) := by
  have hboxes : ∀ᵐ x ∂μ, ∀ ν : Fin q → ℤ,
      x ∈ e ⁻¹' ((BoxIntegral.unitPartition.box n ν) : Set (Fin q → ℝ)) ↔
      x ∈ affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ := by
    rw [ae_all_iff]
    intro ν
    exact (unitPartitionBox_ae_eq_affineHaarCube μ e n ν).mono fun _ hx ↦
      iff_of_eq hx
  filter_upwards [hboxes] with x hx
  let ν := BoxIntegral.unitPartition.index n (e x)
  have hmem : e x ∈ BoxIntegral.unitPartition.box n ν :=
    BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl
  have hopen := (hx ν).mp hmem
  intro l z hz
  have hl : 0 < affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ x l ∧
      affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ x l < 1 :=
    hopen l (mem_univ l)
  rw [affineHaarCubeCoord_unitPartition_apply, hz] at hl
  have h₁ : ν l < z := by exact_mod_cast (show (ν l : ℝ) < z by linarith [hl.1])
  have h₂ : z < ν l + 1 := by exact_mod_cast (show (z : ℝ) < (ν l : ℝ) + 1 by linarith [hl.2])
  omega

/-- The microscopic original integer index of a real macro-grid leaf. -/
def originalMacroMicroIndex (R n : ℕ) (leaf : Fin q → Fin (2 * R * n)) : Fin q → ℤ :=
  fun l ↦ (leaf l : ℕ) - (R * n : ℤ)

theorem originalMacroMicroIndex_injective (R n : ℕ) :
    Injective (originalMacroMicroIndex (q := q) R n) := by
  intro a b hab
  funext l
  apply Fin.ext
  have h := congrFun hab l
  dsimp only [originalMacroMicroIndex] at h
  have hh := sub_left_injective h
  exact_mod_cast hh

/-- At a point off the original coordinate faces, the floor grid and the
literal half-open original microbox name exactly the same cell. -/
theorem grid_leaf_eq_iff_original_microbox
    (basis : Basis (Fin q) ℝ E) {R n depth : ℕ} (hR : 0 < R) (hn : 0 < n)
    (hdepth : 2 * R * n ≤ 2 ^ depth)
    (x : E) (hx : labelCubeCoordinates basis R x ∈ unitCubeSet q)
    (hoff : ∀ l : Fin q, ∀ z : ℤ, (n : ℝ) * basis.equivFun x l ≠ (z : ℝ))
    (leaf : Fin q → Fin (2 * R * n)) :
    let _inst : NeZero n := ⟨hn.ne'⟩
    gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth
      (labelCubeCoordinates basis R x) =
      blockLeafLabel q (2 * R * n) depth hdepth leaf ↔
    basis.equivFun x ∈ BoxIntegral.unitPartition.box n (originalMacroMicroIndex R n leaf) := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  dsimp only
  rw [gridCellLabel_leaf_eq_iff (by positivity) hdepth hx,
    BoxIntegral.unitPartition.mem_box_iff']
  apply forall_congr'
  intro l
  rw [blockIndex_inv_eq_floor]
  have hRr : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hshift : ((2 * R * n : ℕ) : ℝ) * labelCubeCoordinates basis R x l =
      (n : ℝ) * basis.equivFun x l + (R * n : ℕ) := by
    simp only [labelCubeCoordinates, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  have hnonneg : 0 ≤ ((2 * R * n : ℕ) : ℝ) * labelCubeCoordinates basis R x l := by
    have hl := hx l (mem_univ l)
    exact mul_nonneg (Nat.cast_nonneg _) hl.1.le
  rw [Nat.floor_eq_iff hnonneg, hshift]
  have hlow := hoff l (originalMacroMicroIndex R n leaf l)
  have hupp := hoff l (originalMacroMicroIndex R n leaf l + 1)
  simp only [originalMacroMicroIndex, Int.cast_sub, Int.cast_natCast, Int.cast_add,
    Int.cast_one, Int.cast_mul, Nat.cast_mul] at hlow hupp ⊢
  constructor
  · intro h
    constructor
    · exact lt_of_le_of_ne (by linarith [h.1]) (Ne.symm hlow)
    · linarith [h.2]
  · intro h
    constructor
    · linarith [h.1]
    · have hh := lt_of_le_of_ne h.2 hupp
      linarith

/-- Original Haar law discharges the boundary condition in the literal
macro-leaf to physical-microbox identification. -/
theorem ae_grid_leaf_eq_iff_original_microbox
    (μ : Measure E) [μ.IsAddHaarMeasure] (basis : Basis (Fin q) ℝ E)
    {R n depth : ℕ} (hR : 0 < R) (hn : 0 < n)
    (hdepth : 2 * R * n ≤ 2 ^ depth) :
    let _inst : NeZero n := ⟨hn.ne'⟩
    ∀ᵐ x ∂μ, labelCubeCoordinates basis R x ∈ unitCubeSet q →
      ∀ leaf : Fin q → Fin (2 * R * n),
      gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth
        (labelCubeCoordinates basis R x) =
        blockLeafLabel q (2 * R * n) depth hdepth leaf ↔
      basis.equivFun x ∈ BoxIntegral.unitPartition.box n (originalMacroMicroIndex R n leaf) := by
  letI : NeZero n := ⟨hn.ne'⟩
  filter_upwards [ae_original_grid_coordinates_nonintegral μ basis.equivFunL n] with x hx
  intro hunit leaf
  exact grid_leaf_eq_iff_original_microbox basis hR hn hdepth x hunit hx leaf

/-- The same original-index legal graph is selected by its physical microbox.
Only endpoints of allowed edges need satisfy the coordinate carrier. -/
theorem PartialMatching.spatialLegalBlock_grid_leaf_eq_original_microbox
    {s t : ℕ} (allowed : Finset (Fin s × Fin t))
    (xs : Fin s → E) (ys : Fin t → E) (basis : Basis (Fin q) ℝ E)
    {R n depth : ℕ} (hR : 0 < R) (hn : 0 < n)
    (hdepth : 2 * R * n ≤ 2 ^ depth)
    (hunit : ∀ edge ∈ allowed,
      labelCubeCoordinates basis R (xs edge.1) ∈ unitCubeSet q ∧
      labelCubeCoordinates basis R (ys edge.2) ∈ unitCubeSet q)
    (hoff : ∀ edge ∈ allowed, ∀ l : Fin q, ∀ z : ℤ,
      (n : ℝ) * basis.equivFun (xs edge.1) l ≠ (z : ℝ) ∧
      (n : ℝ) * basis.equivFun (ys edge.2) l ≠ (z : ℝ))
    (leaf : Fin q → Fin (2 * R * n)) :
    let _inst : NeZero n := ⟨hn.ne'⟩
    spatialLegalBlock allowed
      (fun j ↦ gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth
        (labelCubeCoordinates basis R (xs j)))
      (fun k ↦ gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth
        (labelCubeCoordinates basis R (ys k)))
      (blockLeafLabel q (2 * R * n) depth hdepth leaf) =
      allowed.filter (fun edge ↦
        basis.equivFun (xs edge.1) ∈
          BoxIntegral.unitPartition.box n (originalMacroMicroIndex R n leaf) ∧
        basis.equivFun (ys edge.2) ∈
          BoxIntegral.unitPartition.box n (originalMacroMicroIndex R n leaf)) := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  ext edge
  simp only [spatialLegalBlock, Finset.mem_filter]
  by_cases he : edge ∈ allowed
  · simp only [he, true_and]
    have hs := grid_leaf_eq_iff_original_microbox basis hR hn hdepth (xs edge.1)
      (hunit edge he).1 (fun l z ↦ (hoff edge he l z).1) leaf
    have ht := grid_leaf_eq_iff_original_microbox basis hR hn hdepth (ys edge.2)
      (hunit edge he).2 (fun l z ↦ (hoff edge he l z).2) leaf
    dsimp only at hs ht
    rw [hs, ht]
  · simp only [he, false_and]

/-- Padded labels carry no original vertex. This exact finite identity applies
to arbitrary allowed graphs and true costs, without a clamped cloud model. -/
theorem PartialMatching.spatialLegalBlock_grid_sum_eq_realBlocks
    {s t : ℕ} (allowed : Finset (Fin s × Fin t)) (cost : Fin s → Fin t → ℝ)
    (xs : Fin s → (Fin q → ℝ)) (ys : Fin t → (Fin q → ℝ))
    {m depth : ℕ} (hm : 0 < m) (hdepth : m ≤ 2 ^ depth) :
    (∑ leaf : Fin q → Fin (2 ^ depth + 1), legalMaximumValue
      (spatialLegalBlock allowed (fun j ↦ gridCellLabel q m depth depth hm hdepth (xs j))
        (fun k ↦ gridCellLabel q m depth depth hm hdepth (ys k)) leaf) cost) =
    ∑ leaf : Fin q → Fin m, legalMaximumValue
      (spatialLegalBlock allowed (fun j ↦ gridCellLabel q m depth depth hm hdepth (xs j))
        (fun k ↦ gridCellLabel q m depth depth hm hdepth (ys k))
        (blockLeafLabel q m depth hdepth leaf)) cost := by
  classical
  let f := fun leaf : Fin q → Fin (2 ^ depth + 1) ↦ legalMaximumValue
    (spatialLegalBlock allowed (fun j ↦ gridCellLabel q m depth depth hm hdepth (xs j))
      (fun k ↦ gridCellLabel q m depth depth hm hdepth (ys k)) leaf) cost
  let S : Finset (Fin q → Fin (2 ^ depth + 1)) :=
    Finset.univ.filter (fun leaf ↦ ∀ l, (leaf l).val < m)
  have hzero : ∀ leaf ∈ (Finset.univ : Finset (Fin q → Fin (2 ^ depth + 1))),
      leaf ∉ S → f leaf = 0 := by
    intro leaf _ hleaf
    obtain ⟨l, hl⟩ : ∃ l, ¬(leaf l).val < m := not_forall.mp (fun h ↦
      hleaf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hempty : spatialLegalBlock allowed
        (fun j ↦ gridCellLabel q m depth depth hm hdepth (xs j))
        (fun k ↦ gridCellLabel q m depth depth hm hdepth (ys k)) leaf = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro edge he
      have heq := (Finset.mem_filter.mp he).2.1
      change gridCellLabel q m depth depth hm hdepth (xs edge.1) = leaf at heq
      have hh := gridCellLabel_leaf_val_lt hm hdepth (xs edge.1) l
      rw [heq] at hh
      exact hl hh
    exact (congrArg (fun graph ↦ legalMaximumValue graph cost) hempty).trans
      (legalMaximumValue_empty cost)
  change (∑ leaf, f leaf) = ∑ leaf : Fin q → Fin m, f (blockLeafLabel q m depth hdepth leaf)
  rw [← Finset.sum_subset (Finset.subset_univ S) hzero]
  let index : (leaf : Fin q → Fin (2 ^ depth + 1)) → leaf ∈ S → (Fin q → Fin m) :=
    fun leaf hleaf l ↦ ⟨(leaf l).val, (Finset.mem_filter.mp hleaf).2 l⟩
  refine Finset.sum_bij (i := index) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro a ha b hb hab
    funext l
    apply Fin.ext
    exact congrArg (fun leaf : Fin q → Fin m ↦ (leaf l).val) hab
  · intro leaf _
    refine ⟨blockLeafLabel q m depth hdepth leaf, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l ↦ blockLeafLabel_lt q m depth hdepth leaf l⟩
    · funext l
      apply Fin.ext
      rfl
  · intro leaf hleaf
    apply congrArg f
    funext l
    apply Fin.ext
    rfl

end OTSelector.Reconstruction
