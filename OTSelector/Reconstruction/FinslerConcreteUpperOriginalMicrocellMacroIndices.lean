import OTSelector.Reconstruction.FinslerConcreteUpperOriginalMacroGridCells

/-! Removing boxes which miss the original measurable cell preserves its
literal trace. Every remaining original microbox has a genuine macro leaf. -/
open Set Function MeasureTheory BoxIntegral
open scoped Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
variable {q : ℕ}

/-- Only boxes meeting the literal original coordinate cell are kept. -/
def originalMeetingMicrocells (n : ℕ) [NeZero n]
    (s : Set (Fin q → ℝ)) (cells : Finset (Fin q → ℤ)) : Finset (Fin q → ℤ) :=
  cells.filter (fun ν ↦ ((unitPartition.box n ν : Set (Fin q → ℝ)) ∩ s).Nonempty)

/-- This finite filtering leaves the entire retained original trace unchanged. -/
theorem originalMeetingMicrocells_trace (n : ℕ) [NeZero n]
    (s : Set (Fin q → ℝ)) (cells : Finset (Fin q → ℤ)) :
    s ∩ (⋃ ν ∈ originalMeetingMicrocells n s cells,
      (unitPartition.box n ν : Set (Fin q → ℝ))) =
    s ∩ (⋃ ν ∈ cells, (unitPartition.box n ν : Set (Fin q → ℝ))) := by
  ext x
  constructor
  · rintro ⟨hs,hx⟩
    obtain ⟨ν,hν,hxν⟩ := mem_iUnion₂.mp hx
    exact ⟨hs,mem_iUnion₂.mpr ⟨ν,(Finset.mem_filter.mp hν).1,hxν⟩⟩
  · rintro ⟨hs,hx⟩
    obtain ⟨ν,hν,hxν⟩ := mem_iUnion₂.mp hx
    exact ⟨hs,mem_iUnion₂.mpr ⟨ν,Finset.mem_filter.mpr ⟨hν,⟨x,hxν,hs⟩⟩,hxν⟩⟩

/-- Added full-box volume only decreases under the trace-preserving filter. -/
theorem originalMeetingMicrocells_added_subset (n : ℕ) [NeZero n]
    (s : Set (Fin q → ℝ)) (cells : Finset (Fin q → ℤ)) :
    ((⋃ ν ∈ originalMeetingMicrocells n s cells,
      (unitPartition.box n ν : Set (Fin q → ℝ))) \ s) ⊆
    ((⋃ ν ∈ cells, (unitPartition.box n ν : Set (Fin q → ℝ))) \ s) := by
  apply sdiff_subset_sdiff_left
  intro x hx
  obtain ⟨ν,hν,hxν⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨ν,(Finset.mem_filter.mp hν).1,hxν⟩

/-- Any original half-open microbox meeting an open integer macrobox has
index in the literal range of the actual macro leaves. -/
theorem original_microcell_index_bounds_of_meets_macro
    {R n : ℕ} [NeZero n] {s : Set (Fin q → ℝ)}
    (hmacro : ∀ x ∈ s, ∀ l, -(R : ℝ) < x l ∧ x l < R)
    {ν : Fin q → ℤ} (hmeet : ((unitPartition.box n ν : Set (Fin q → ℝ)) ∩ s).Nonempty) :
    ∀ l, -(R * n : ℤ) ≤ ν l ∧ ν l < (R * n : ℤ) := by
  obtain ⟨x,hx,hxs⟩ := hmeet
  have hbox := unitPartition.mem_box_iff'.mp hx
  intro l
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos_of_neZero
  have hlo := mul_lt_mul_of_pos_left (hmacro x hxs l).1 hn
  have hup := mul_lt_mul_of_pos_left (hmacro x hxs l).2 hn
  have hlo' : -(R * n : ℤ) < ν l + 1 := by
    have hh : -((R : ℝ) * n) < (ν l : ℝ) + 1 := by nlinarith [(hbox l).2]
    exact_mod_cast hh
  have hup' : ν l < (R * n : ℤ) := by
    have hh : (ν l : ℝ) < (R : ℝ) * n := by nlinarith [(hbox l).1]
    exact_mod_cast hh
  exact ⟨by omega,hup'⟩

/-- The original integer range is encoded by a real macro leaf, without
altering the physical microbox or its original side length. -/
theorem exists_originalMacroMicroIndex_eq {R n : ℕ} {ν : Fin q → ℤ}
    (hν : ∀ l, -(R * n : ℤ) ≤ ν l ∧ ν l < (R * n : ℤ)) :
    ∃ leaf : Fin q → Fin (2 * R * n), originalMacroMicroIndex R n leaf = ν := by
  let leaf : Fin q → Fin (2 * R * n) := fun l ↦
    ⟨(ν l + (R * n : ℤ)).toNat, by
      have hnonneg : 0 ≤ ν l + (R * n : ℤ) := by linarith [(hν l).1]
      have hlt : ν l + (R * n : ℤ) < (2 * R * n : ℕ) := by
        norm_num only [Nat.cast_mul,Nat.cast_ofNat]
        nlinarith [(hν l).2]
      have hh : ((ν l + (R * n : ℤ)).toNat : ℤ) < (2 * R * n : ℕ) := by
        simpa only [Int.toNat_of_nonneg hnonneg] using hlt
      exact_mod_cast hh⟩
  refine ⟨leaf,?_⟩
  funext l
  change ((ν l + (R * n : ℤ)).toNat : ℤ) - (R * n : ℤ) = ν l
  rw [Int.toNat_of_nonneg (by linarith [(hν l).1])]
  omega

/-- Every filtered box in the original cell approximation is one literal
macro leaf. No additional macro-containment assumption on the approximation
or eventual deletion of original points is required. -/
theorem originalMeetingMicrocells_subset_macro_range
    {R n : ℕ} [NeZero n] {s : Set (Fin q → ℝ)}
    (hmacro : ∀ x ∈ s, ∀ l, -(R : ℝ) < x l ∧ x l < R)
    (cells : Finset (Fin q → ℤ)) :
    originalMeetingMicrocells n s cells ⊆
      Finset.univ.image (originalMacroMicroIndex (q := q) R n) := by
  intro ν hν
  obtain ⟨leaf,hindex⟩ := exists_originalMacroMicroIndex_eq
    (original_microcell_index_bounds_of_meets_macro hmacro (Finset.mem_filter.mp hν).2)
  exact Finset.mem_image.mpr ⟨leaf,Finset.mem_univ _,hindex⟩

/-- A supported original active graph has exactly the selected physical
microbox values as its padded leaf sum. Signed true costs are kept literal;
neither cardinality nor kinetic cost is replaced. -/
theorem PartialMatching.sum_macro_grid_leaves_eq_original_microcells
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {s t : ℕ} (allowed : Finset (Fin s × Fin t)) (cost : Fin s → Fin t → ℝ)
    (xs : Fin s → E) (ys : Fin t → E) (basis : Module.Basis (Fin q) ℝ E)
    {R n depth : ℕ} (hR : 0 < R) (hn : 0 < n)
    (hdepth : 2 * R * n ≤ 2 ^ depth)
    (hunit : ∀ edge ∈ allowed,
      labelCubeCoordinates basis R (xs edge.1) ∈ OTSelector.Probability.unitCubeSet q ∧
      labelCubeCoordinates basis R (ys edge.2) ∈ OTSelector.Probability.unitCubeSet q)
    (hoff : ∀ edge ∈ allowed, ∀ l : Fin q, ∀ z : ℤ,
      (n : ℝ) * basis.equivFun (xs edge.1) l ≠ (z : ℝ) ∧
      (n : ℝ) * basis.equivFun (ys edge.2) l ≠ (z : ℝ))
    (cells : Finset (Fin q → ℤ))
    (hfit : cells ⊆ Finset.univ.image (originalMacroMicroIndex (q := q) R n)) :
    let _inst : NeZero n := ⟨hn.ne'⟩
    (∀ edge ∈ allowed, basis.equivFun (xs edge.1) ∈
      ⋃ ν ∈ cells, (unitPartition.box n ν : Set (Fin q → ℝ))) →
    (∑ leaf : Fin q → Fin (2 ^ depth + 1), legalMaximumValue
      (spatialLegalBlock allowed
        (fun j ↦ OTSelector.Probability.gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth
          (labelCubeCoordinates basis R (xs j)))
        (fun k ↦ OTSelector.Probability.gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth
          (labelCubeCoordinates basis R (ys k))) leaf) cost) =
      ∑ ν ∈ cells, legalMaximumValue (allowed.filter (fun edge ↦
        basis.equivFun (xs edge.1) ∈ unitPartition.box n ν ∧
        basis.equivFun (ys edge.2) ∈ unitPartition.box n ν)) cost := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  dsimp only
  intro hsource
  let value := fun ν : Fin q → ℤ ↦ legalMaximumValue (allowed.filter (fun edge ↦
    basis.equivFun (xs edge.1) ∈ unitPartition.box n ν ∧
    basis.equivFun (ys edge.2) ∈ unitPartition.box n ν)) cost
  rw [spatialLegalBlock_grid_sum_eq_realBlocks allowed cost
    (fun j ↦ labelCubeCoordinates basis R (xs j)) (fun k ↦ labelCubeCoordinates basis R (ys k))
    (by positivity) hdepth]
  have hreplace (leaf : Fin q → Fin (2 * R * n)) : legalMaximumValue
      (spatialLegalBlock allowed
        (fun j ↦ OTSelector.Probability.gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth
          (labelCubeCoordinates basis R (xs j)))
        (fun k ↦ OTSelector.Probability.gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth
          (labelCubeCoordinates basis R (ys k)))
        (OTSelector.Probability.blockLeafLabel q (2 * R * n) depth hdepth leaf)) cost =
        value (originalMacroMicroIndex R n leaf) := by
    have hgraph := spatialLegalBlock_grid_leaf_eq_original_microbox allowed xs ys basis hR hn hdepth
      hunit hoff leaf
    dsimp only at hgraph
    rw [hgraph]
  simp_rw [hreplace]
  have hzero : ∀ ν ∈ Finset.univ.image (originalMacroMicroIndex (q := q) R n),
      ν ∉ cells → value ν = 0 := by
    intro ν _ hν
    have hempty : allowed.filter (fun edge ↦
        basis.equivFun (xs edge.1) ∈ unitPartition.box n ν ∧
        basis.equivFun (ys edge.2) ∈ unitPartition.box n ν) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro edge he
      obtain ⟨ν',hν',hmem⟩ := mem_iUnion₂.mp (hsource edge (Finset.mem_filter.mp he).1)
      have hmem' := (Finset.mem_filter.mp he).2.1
      have heq : ν = ν' := (unitPartition.mem_box_iff_index.mp hmem').symm.trans
        (unitPartition.mem_box_iff_index.mp hmem)
      exact hν (heq.symm ▸ hν')
    exact (congrArg (fun graph ↦ legalMaximumValue graph cost) hempty).trans
      (legalMaximumValue_empty cost)
  calc
    _ = ∑ ν ∈ Finset.univ.image (originalMacroMicroIndex (q := q) R n), value ν := by
      symm
      exact Finset.sum_image (fun a _ b _ hab ↦ originalMacroMicroIndex_injective R n hab)
    _ = _ := (Finset.sum_subset hfit hzero).symm

end OTSelector.Reconstruction
