import OTSelector.Reconstruction.FinslerCoefficientCorePartition

/-!
# Finite measurable scalar bins for original transport types

Compact scalar ranges admit a disjoint measurable subdivision of prescribed
small diameter. One calibrated pair with the original support gap then separates
all source and target scalars in its two bins. Endpoint sets are not closed.
-/

open Set MeasureTheory Metric

noncomputable section
namespace OTSelector.Reconstruction

/-- A finite measurable partition with bin diameter at most one quarter of the
original support separation. The cells need not be closed. -/
structure FiniteScalarBins (I : Set ℝ) (δ : ℝ) where
  count : ℕ
  cell : Fin count → Set ℝ
  measurable_cell : ∀ i, MeasurableSet (cell i)
  subset : ∀ i, cell i ⊆ I
  disjoint : Pairwise (fun i j ↦ Disjoint (cell i) (cell j))
  union_eq : (⋃ i, cell i) = I
  diameter : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i, |x - y| ≤ δ / 4

/-- Compactness produces finitely many actual measurable bins of the required
width, preserving every scalar in the original compact range. -/
theorem exists_finiteScalarBins {I : Set ℝ} (hI : IsCompact I)
    {δ : ℝ} (hδ : 0 < δ) : Nonempty (FiniteScalarBins I δ) := by
  obtain ⟨centers, _, hfinite, hcover⟩ := hI.elim_finite_subcover_image
    (b := I) (c := fun x ↦ ball x (δ / 8)) (fun _ _ ↦ isOpen_ball) (by
      intro x hx
      exact mem_iUnion₂.mpr ⟨x, hx, mem_ball_self (by positivity)⟩)
  obtain ⟨Q⟩ := exists_finiteRootNeighborhoodPartition hI.measurableSet hfinite
    (fun _ _ ↦ isOpen_ball.measurableSet) hcover
  refine ⟨{
    count := Q.count
    cell := Q.cell
    measurable_cell := Q.measurable_cell
    subset := fun i ↦ (Q.cell_subset i).trans inter_subset_left
    disjoint := Q.disjoint
    union_eq := Q.union_eq
    diameter := ?_ }⟩
  intro i x hx y hy
  have hx' := mem_ball.mp (Q.cell_subset i hx).2
  have hy' := mem_ball.mp (Q.cell_subset i hy).2
  have hb := (dist_triangle x (Q.center i) y).trans_lt
    (add_lt_add hx' (by simpa only [dist_comm] using hy'))
  rw [Real.dist_eq] at hb
  linarith

/-- One original calibrated pair separates the full two bins, losing at most
one quarter of the support gap at each endpoint. -/
theorem FiniteScalarBins.gap_of_same_bins {I : Set ℝ} {δ : ℝ}
    (D : FiniteScalarBins I δ) {i j : Fin D.count} {a b : ℝ}
    (ha : a ∈ D.cell i) (hb : b ∈ D.cell j) (hgap : δ ≤ b - a)
    {x y : ℝ} (hx : x ∈ D.cell i) (hy : y ∈ D.cell j) : δ / 2 ≤ y - x := by
  have hx' := (abs_le.mp (D.diameter i x hx a ha)).2
  have hy' := (abs_le.mp (D.diameter j y hy b hb)).1
  linarith

/-- A positive original transport type contains an actual separated pair, so its
whole source bin lies below its whole target bin by half the original gap. -/
theorem FiniteScalarBins.gap_of_type_mass_ne_zero {I : Set ℝ} {δ : ℝ}
    (D : FiniteScalarBins I δ) {X : Type*} [MeasurableSpace X]
    (π : Measure X) {source target : X → ℝ} {A : Set X}
    {i j : Fin D.count}
    (hA : ∀ p ∈ A, source p ∈ D.cell i ∧ target p ∈ D.cell j)
    (hmass : π A ≠ 0) (hgap : ∀ᵐ p ∂π, δ ≤ target p - source p) :
    ∀ x ∈ D.cell i, ∀ y ∈ D.cell j, δ / 2 ≤ y - x := by
  obtain ⟨p, hp, hpgap⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass
    (ae_restrict_of_ae hgap)
  exact fun x hx y hy ↦ D.gap_of_same_bins (hA p hp).1 (hA p hp).2 hpgap hx hy

/-- The finite scalar bins preserve every original scalar measure exactly. -/
theorem FiniteScalarBins.sum_restrict {I : Set ℝ} {δ : ℝ}
    (D : FiniteScalarBins I δ) (μ : Measure ℝ) :
    Measure.sum (fun i ↦ μ.restrict (D.cell i)) = μ.restrict I := by
  rw [← Measure.restrict_iUnion D.disjoint D.measurable_cell, D.union_eq]

end OTSelector.Reconstruction
