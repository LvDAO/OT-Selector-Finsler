import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveGridArithmetic

/-! Original coordinate bounds produce all active parent-scale cost budgets.
Only endpoints of actual allowed edges must belong to the enclosing cube. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Actual coordinate quadratic control supplies each grid parent budget;
no separate family of parent-scale cost assumptions is required. -/
theorem abs_cost_le_grid_parent_of_quadratic
    (q m depth k : ℕ) (hm : 0 < m) (hdepth : m ≤ 2 ^ depth)
    (hdepth2 : 2 ^ depth ≤ 2 * m) (hk : k ≤ depth)
    {r C G t c : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (x y : Fin q → ℝ) (hx : x ∈ unitCube q) (hy : y ∈ unitCube q)
    (hcost : |c| ≤ r ^ (2 / (q : ℝ)) * (C * ∑ l, (x l - y l) ^ 2) + |t| * G)
    (hcell : gridCellLabel q m depth k hm hdepth x = gridCellLabel q m depth k hm hdepth y) :
    |c| ≤ legalGridEdgeBound q r C G t k := by
  have hcoordX (l) : 0 ≤ x l ∧ x l < 1 := by
    have h := Set.mem_pi.mp hx l (mem_univ l)
    exact ⟨h.1.le, h.2⟩
  have hcoordY (l) : 0 ≤ y l ∧ y l < 1 := by
    have h := Set.mem_pi.mp hy l (mem_univ l)
    exact ⟨h.1.le, h.2⟩
  have hsum := gridCellLabel_sqDist_le hm hdepth hdepth2 hk hcoordX hcoordY hcell
  refine hcost.trans ?_
  calc
    _ ≤ r ^ (2 / (q : ℝ)) *
        (C * (16 * (q : ℝ) * (1 / 4 : ℝ) ^ k)) + |t| * G :=
      add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum hC) (Real.rpow_nonneg hr _)) le_rfl
    _ = _ := by unfold legalGridEdgeBound; ring

namespace PartialMatching

/-- The actual active legal minimum admits the original padded grid repair
with all parent budgets derived from its single coordinate quadratic bound.
Inactive original points may lie outside the cube. -/
theorem legalMaximumValue_le_active_grid_of_quadratic
    {a b : ℕ} {T J : Type*} [Fintype T] [DecidableEq T] [Fintype J]
    (q m depth : ℕ) (hm : 0 < m) (hdepth : m ≤ 2 ^ depth)
    (hdepth2 : 2 ^ depth ≤ 2 * m)
    (allowed : Finset (Fin a × Fin b)) (tagS : Fin a → Option T) (tagT : Fin b → Option T)
    (hactive : ∀ e ∈ allowed, (tagS e.1).isSome = true ∧ (tagT e.2).isSome = true)
    (x : Fin a → Fin q → ℝ) (y : Fin b → Fin q → ℝ)
    (hunit : ∀ e ∈ allowed, x e.1 ∈ unitCube q ∧ y e.2 ∈ unitCube q)
    (sourceClass : Fin a → J) (sourceAllows : J → Fin b → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin a → Fin b → ℝ) {r C G t : ℝ}
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hcost : ∀ i j, (i, j) ∈ allowed → |c i j| ≤
      r ^ (2 / (q : ℝ)) * (C * ∑ l, (x i l - y j l) ^ 2) + |t| * G) :
    legalMaximumValue allowed c ≤
      (∑ z : Fin q → Fin (2 ^ depth + 1), legalMaximumValue
        (spatialLegalBlock allowed (fun i ↦ gridCellLabel q m depth depth hm hdepth (x i))
          (fun j ↦ gridCellLabel q m depth depth hm hdepth (y j)) z) c) +
      ∑ k ∈ Finset.range depth,
        ((∑ z : T, (blockSizeS tagS (some z) : ℝ)) -
          ∑ z : Fin q → Fin (2 ^ (k + 1) + 1), (legalMaximumCard
            (spatialLegalBlock allowed (fun i ↦ gridCellLabel q m depth (k + 1) hm hdepth (x i))
              (fun j ↦ gridCellLabel q m depth (k + 1) hm hdepth (y j)) z) : ℝ)) *
          (2 * (Fintype.card (Option J) : ℝ) * legalGridEdgeBound q r C G t k) := by
  let s := fun k i ↦ gridCellLabel q m depth k hm hdepth (x i)
  let u := fun k j ↦ gridCellLabel q m depth k hm hdepth (y j)
  exact legalMaximumValue_le_active_hierarchical_blocks_upto allowed tagS tagT hactive
    s u (fun k ↦ legalGridParent q m depth k hm hdepth) depth
    (fun k hk i ↦ legalGridParent_cell q m depth k hm hdepth (Nat.succ_le_of_lt hk) _)
    (fun k hk j ↦ legalGridParent_cell q m depth k hm hdepth (Nat.succ_le_of_lt hk) _)
    sourceClass sourceAllows hallowed c (legalGridEdgeBound q r C G t)
    (fun k ↦ legalGridEdgeBound_nonneg q k hr hC hG)
    (fun k hk i j hij hcell ↦ abs_cost_le_grid_parent_of_quadratic q m depth k
      hm hdepth hdepth2 hk.le hr hC (x i) (y j) (hunit _ hij).1 (hunit _ hij).2
      (hcost i j hij) hcell)
    (gridCellLabel q m depth 0 hm hdepth (fun _ ↦ 0))
    (fun _ ↦ gridCellLabel_root hm hdepth _ _) (fun _ ↦ gridCellLabel_root hm hdepth _ _)

end PartialMatching
end OTSelector.Reconstruction
