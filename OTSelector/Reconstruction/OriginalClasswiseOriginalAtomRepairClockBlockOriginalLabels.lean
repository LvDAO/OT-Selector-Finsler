import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabOriginalPlan
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockBlockGraph

/-! The retained original finite matching preserves the actual clock-block labels. -/
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The same original scene and the literal retained-plan representation
force every retained pair's actual block labels to agree. This is derived from
the genuine Palm coupling and tight-cut exclusion, rather than an extra core premise. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalIndex_edges_same_clockBlockLabel
    {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (G : OriginalStageClockGrid) {δ diameter : ℝ} (hδ : 0 < δ)
    (hsep : ConditionalClockSupportBounds μ ν δ diameter)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i)
    (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (h₀ : G.clockSlabSurplus μ ν 0 = 0) (hN : G.clockSlabSurplus μ ν G.count = 0) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ (A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))) (m n : ℕ)
        (x : Fin m → LegalMarkedPhysicalPoint q) (y : Fin n → LegalMarkedPhysicalPoint q)
        (hx : ∀ i, G.sourceLabel (x i).2 < G.count)
        (hy : ∀ j, G.targetLabel (y j).2 < G.count) (σ : OTSelector.PartialMatching m n),
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)) =
          ∑ ij ∈ σ.edges, Measure.dirac (x ij.1, y ij.2) →
      ∀ ij ∈ σ.edges, G.sourceBlockLabel h₀ hN (x ij.1).2 (hx ij.1) =
        G.targetBlockLabel h₀ hN (y ij.2).2 (hy ij.2) := by
  filter_upwards [Q.ae_originalIndex_edges_same_clockSlabBlock G hδ hsep hs ht hmono]
    with scene hscene
  intro A m n x y hx hy σ hσ ij hij
  let b := G.sourceBlockLabel h₀ hN (x ij.1).2 (hx ij.1)
  have hsB : (x ij.1).2 ∈ G.sourceBlockCell μ ν b :=
    (G.sourceBlockLabel_eq_iff_mem h₀ hN _ _ b).mp rfl
  have htB := (hscene A m n x y σ hσ b ij hij).mp hsB
  exact ((G.targetBlockLabel_eq_iff_mem h₀ hN _ _ b).mpr htB).symm

end OTSelector.Reconstruction
