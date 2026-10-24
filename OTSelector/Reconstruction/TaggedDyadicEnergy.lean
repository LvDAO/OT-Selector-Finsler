import OTSelector.Reconstruction.TaggedDyadicHierarchy

/-!
# Actual energy charged to a fixed population type

One full permutation controls internal dyadic matching and cross-type completion.
The latter is charged by that type's original count discrepancy, with the bounded
physical edge cost. This is the deterministic part of subplan energy attribution.
-/

open Function
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

def typeTouchIndicator {T : Type*} (t a b : T) : ℝ := by
  classical
  exact if a = t ∨ b = t then 1 else 0

def typeInternalMask {T : Type*} (t a b : T) : ℝ := by
  classical
  exact if a = t ∧ b = t then 1 else 0

/-- Energy of edges incident to one type; cross-type edges may be charged to
both endpoint types, which is appropriate for an upper bound. -/
def attributedTypeEnergy {T : Type*} {q n : ℕ} (t : T)
    (x y : Fin n → T × DyadicUnitCube q) (cost : Fin n → Fin n → ℝ)
    (σ : Assignment n) : ℝ :=
  ∑ i, typeTouchIndicator t (x i).1 (y (σ i)).1 * cost i (σ i)

/-- The refined original histogram discrepancy of a single population type. -/
def taggedDyadicDiscrepancy {T : Type*} {q n : ℕ} (t : T) (k : ℕ)
    (x y : Fin n → T × DyadicUnitCube q) : ℝ :=
  ∑ a, |partitionCount (fun i ↦ ((x i).1, dyadicCubeCell k (x i).2)) (t, a) -
    partitionCount (fun i ↦ ((y i).1, dyadicCubeCell k (y i).2)) (t, a)|

private theorem typeTouch_cost_le {T : Type*} {q : ℕ} (t : T)
    (x y : T × DyadicUnitCube q) (c C B : ℝ) (hB : c ≤ B)
    (hC : x.1 = t → y.1 = t → c ≤ C * ‖dyadicCubePoint x.2 - dyadicCubePoint y.2‖ ^ 2) :
    typeTouchIndicator t x.1 y.1 * c ≤
      C * (typeInternalMask t x.1 y.1 * ‖dyadicCubePoint x.2 - dyadicCubePoint y.2‖ ^ 2) +
      B * typeCrossingCharge t x.1 y.1 := by
  classical
  by_cases hx : x.1 = t <;> by_cases hy : y.1 = t
  · simpa [typeTouchIndicator, typeInternalMask, typeCrossingCharge, partitionIndicator, hx, hy]
      using hC hx hy
  · simpa [typeTouchIndicator, typeInternalMask, typeCrossingCharge, partitionIndicator, hx, hy]
      using hB
  · simpa [typeTouchIndicator, typeInternalMask, typeCrossingCharge, partitionIndicator, hx, hy]
      using hB
  · simp [typeTouchIndicator, typeInternalMask, typeCrossingCharge, partitionIndicator, hx, hy]

private theorem typeInternal_sqdist_multiscale {T : Type*} {q : ℕ} (t : T) (N : ℕ)
    (x y : T × DyadicUnitCube q) :
    typeInternalMask t x.1 y.1 * ‖dyadicCubePoint x.2 - dyadicCubePoint y.2‖ ^ 2 ≤
      partitionIndicator x.1 t * (1 / 4 : ℝ) ^ N +
      ∑ k ∈ Finset.range N, (1 / 4 : ℝ) ^ k *
        typeInternalCrossing t (x.1, dyadicCubeCell (k + 1) x.2)
          (y.1, dyadicCubeCell (k + 1) y.2) := by
  classical
  by_cases hx : x.1 = t <;> by_cases hy : y.1 = t
  · simpa [typeInternalMask, typeInternalCrossing, partitionIndicator, hx, hy]
      using dyadicCube_sqdist_multiscale N x.2 y.2
  · simp [typeInternalMask, typeInternalCrossing, partitionIndicator, hx, hy]
  · simp [typeInternalMask, typeInternalCrossing, partitionIndicator, hx, hy]
  · simp [typeInternalMask, typeInternalCrossing, partitionIndicator, hx, hy]

/-- A single hierarchy optimizer admits a typewise finite-depth cost bound.
All types may choose different cutoffs below its common depth K. -/
theorem taggedHierarchy_attributed_energy_le
    {T : Type*} {q n K N : ℕ} (hNK : N ≤ K) (t : T)
    (x y : Fin n → T × DyadicUnitCube q) {σ : Assignment n}
    (hσ : OptimalAssignment (taggedHierarchyCost K x y) σ)
    (cost : Fin n → Fin n → ℝ) (C B : ℝ) (hC0 : 0 ≤ C)
    (hbound : ∀ i j, cost i j ≤ B)
    (hquadratic : ∀ i j, (x i).1 = t → (y j).1 = t →
      cost i j ≤ C * ‖dyadicCubePoint (x i).2 - dyadicCubePoint (y j).2‖ ^ 2) :
    attributedTypeEnergy t x y cost σ ≤
      C * (partitionCount (fun i ↦ (x i).1) t * (1 / 4 : ℝ) ^ N +
        (1 / 2 : ℝ) * ∑ k ∈ Finset.range N,
          (1 / 4 : ℝ) ^ k * taggedDyadicDiscrepancy t (k + 1) x y) +
      B * |partitionCount (fun i ↦ (x i).1) t - partitionCount (fun i ↦ (y i).1) t| := by
  classical
  have hcross := sum_typeCrossingCharge_eq (fun i ↦ (x i).1) (fun i ↦ (y i).1) σ
    (taggedHierarchy_type_no_opposite x y hσ) t
  have hcell (k : ℕ) (hk : k ∈ Finset.range N) :
      (∑ i, typeInternalCrossing t ((x i).1, dyadicCubeCell (k + 1) (x i).2)
        ((y (σ i)).1, dyadicCubeCell (k + 1) (y (σ i)).2)) ≤
      (1 / 2 : ℝ) * taggedDyadicDiscrepancy t (k + 1) x y := by
    have hkK : k + 1 ≤ K := by have := Finset.mem_range.mp hk; omega
    have h := typeInternalCrossing_le_histogram
      (fun i ↦ ((x i).1, dyadicCubeCell (k + 1) (x i).2))
      (fun i ↦ ((y i).1, dyadicCubeCell (k + 1) (y i).2)) σ
      (taggedHierarchy_cell_no_opposite (by omega) hkK x y hσ) t
    change 2 * _ ≤ taggedDyadicDiscrepancy t (k + 1) x y at h
    linarith
  have hint : (∑ i, typeInternalMask t (x i).1 (y (σ i)).1 *
      ‖dyadicCubePoint (x i).2 - dyadicCubePoint (y (σ i)).2‖ ^ 2) ≤
      partitionCount (fun i ↦ (x i).1) t * (1 / 4 : ℝ) ^ N +
        (1 / 2 : ℝ) * ∑ k ∈ Finset.range N,
          (1 / 4 : ℝ) ^ k * taggedDyadicDiscrepancy t (k + 1) x y := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ ↦ typeInternal_sqdist_multiscale t N (x i) (y (σ i)))
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at hs
    rw [Finset.sum_comm] at hs
    have he : (∑ k ∈ Finset.range N, ∑ i,
        (1 / 4 : ℝ) ^ k * typeInternalCrossing t ((x i).1, dyadicCubeCell (k + 1) (x i).2)
          ((y (σ i)).1, dyadicCubeCell (k + 1) (y (σ i)).2)) ≤
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range N,
        (1 / 4 : ℝ) ^ k * taggedDyadicDiscrepancy t (k + 1) x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      rw [← Finset.mul_sum]
      convert mul_le_mul_of_nonneg_left (hcell k hk) (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k) using 1
      ring
    exact hs.trans (add_le_add le_rfl he)
  have ht := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ ↦ typeTouch_cost_le t (x i) (y (σ i)) (cost i (σ i)) C B
      (hbound i (σ i)) (hquadratic i (σ i)))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at ht
  rw [hcross] at ht
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_left hint hC0) le_rfl)

end OTSelector.Reconstruction
