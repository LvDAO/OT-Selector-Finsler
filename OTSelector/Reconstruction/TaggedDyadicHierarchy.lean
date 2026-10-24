import OTSelector.Reconstruction.DyadicCubePartition
import OTSelector.Reconstruction.HierarchicalTypedDiscrepancy
import OTSelector.Finite.CostOptimizer

/-!
# A single hierarchy for all original population types

The first level records only the type. Finer levels retain that same type and
its actual dyadic cube cell. One full optimizer therefore controls both global
count completion and every type's internal matching cost.
-/

open Set Function MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Level zero records the original type; positive levels refine within it. -/
def taggedDyadicCell {T : Type*} {q : ℕ} (k : ℕ) (x : T × DyadicUnitCube q) :
    T × (Fin q → Fin (2 ^ k + 1)) := by
  classical
  exact (x.1, if k = 0 then 0 else dyadicCubeCell k x.2)

theorem taggedDyadicCell_zero_eq_iff {T : Type*} {q : ℕ} (x y : T × DyadicUnitCube q) :
    taggedDyadicCell 0 x = taggedDyadicCell 0 y ↔ x.1 = y.1 := by
  simp [taggedDyadicCell]

theorem taggedDyadicCell_pos {T : Type*} {q k : ℕ} (hk : 0 < k)
    (x : T × DyadicUnitCube q) :
    taggedDyadicCell k x = (x.1, dyadicCubeCell k x.2) := by
  simp [taggedDyadicCell, Nat.ne_of_gt hk]

/-- Actual type-and-cell labels form a nested finite hierarchy. -/
theorem taggedDyadicCell_nested {T : Type*} {q k l : ℕ} (hkl : k ≤ l)
    (x y : T × DyadicUnitCube q) (hxy : taggedDyadicCell l x = taggedDyadicCell l y) :
    taggedDyadicCell k x = taggedDyadicCell k y := by
  have htag : x.1 = y.1 := by
    simpa only [taggedDyadicCell] using congrArg Prod.fst hxy
  by_cases hk : k = 0
  · subst k
    exact (taggedDyadicCell_zero_eq_iff x y).mpr htag
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  have hl0 : 0 < l := lt_of_lt_of_le hk0 hkl
  rw [taggedDyadicCell_pos hk0, taggedDyadicCell_pos hk0]
  rw [taggedDyadicCell_pos hl0, taggedDyadicCell_pos hl0] at hxy
  exact Prod.ext htag (dyadicCubeCell_nested hkl x.2 y.2 (congrArg Prod.snd hxy))

/-- The type-and-cell map is measurable on the unchanged marked sample. -/
theorem measurable_taggedDyadicCell {T : Type*} [MeasurableSpace T] {q : ℕ} (k : ℕ) :
    Measurable (taggedDyadicCell (T := T) (q := q) k) := by
  classical
  unfold taggedDyadicCell
  by_cases hk : k = 0
  · subst k
    simpa using
      (measurable_fst.prodMk (measurable_const : Measurable (fun _ : T × DyadicUnitCube q ↦
        (0 : Fin q → Fin (2 ^ 0 + 1)))))
  · simpa [hk] using
      measurable_fst.prodMk ((measurable_dyadicCubeCell k).comp measurable_snd)

/-- One finite hierarchy objective, including the initial population type. -/
def taggedHierarchyCost {T : Type*} {q n : ℕ} (K : ℕ)
    (x y : Fin n → T × DyadicUnitCube q) : Fin n → Fin n → ℝ :=
  hierarchyEdgeCost (fun k : Fin (K + 1) ↦ taggedDyadicCell k.val) x y

/-- Every optimizer of the one hierarchy saturates the original types. -/
theorem taggedHierarchy_type_no_opposite
    {T : Type*} {q n K : ℕ} (x y : Fin n → T × DyadicUnitCube q)
    {σ : Assignment n} (hσ : OptimalAssignment (taggedHierarchyCost K x y) σ)
    (i j : Fin n) (hin : (x i).1 = (y (σ j)).1) (hout : (x i).1 ≠ (y (σ i)).1) :
    (x j).1 = (y (σ j)).1 := by
  have h := hierarchy_optimal_no_opposite_crossings
    (fun k : Fin (K + 1) ↦ taggedDyadicCell (T := T) (q := q) k.val)
    (fun _ _ hkl a b hab ↦ taggedDyadicCell_nested hkl a b hab) x y hσ (0 : Fin (K + 1)) i j
  apply (taggedDyadicCell_zero_eq_iff (x j) (y (σ j))).mp
  exact h ((taggedDyadicCell_zero_eq_iff _ _).mpr hin)
    (fun he ↦ hout ((taggedDyadicCell_zero_eq_iff _ _).mp he))

/-- The same optimizer saturates every actual dyadic cell of every type. -/
theorem taggedHierarchy_cell_no_opposite
    {T : Type*} {q n K k : ℕ} (hk : 0 < k) (hkK : k ≤ K)
    (x y : Fin n → T × DyadicUnitCube q)
    {σ : Assignment n} (hσ : OptimalAssignment (taggedHierarchyCost K x y) σ)
    (i j : Fin n)
    (hin : ((x i).1, dyadicCubeCell k (x i).2) =
      ((y (σ j)).1, dyadicCubeCell k (y (σ j)).2))
    (hout : ((x i).1, dyadicCubeCell k (x i).2) ≠
      ((y (σ i)).1, dyadicCubeCell k (y (σ i)).2)) :
    ((x j).1, dyadicCubeCell k (x j).2) =
      ((y (σ j)).1, dyadicCubeCell k (y (σ j)).2) := by
  have h := hierarchy_optimal_no_opposite_crossings
    (fun l : Fin (K + 1) ↦ taggedDyadicCell (T := T) (q := q) l.val)
    (fun _ _ hlm a b hab ↦ taggedDyadicCell_nested hlm a b hab) x y hσ
    (⟨k, by omega⟩ : Fin (K + 1)) i j
  simp only [taggedDyadicCell_pos hk] at h
  exact h hin hout

end OTSelector.Reconstruction
