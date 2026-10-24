import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoEdgeSwap
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCompleteGridCells
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.Topology.DiscreteSubset

/-!
# Actual coarse-grid cell pieces form a locally finite family

The existing coordinate lattice is a closed discrete subgroup of Euclidean
space. Its bounded closed cell translates are locally finite. Consequently
the original complete-cell restrictions, and their within-cell crossed swaps,
have a literal locally finite measure sum, with no moment hypothesis.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- The existing full coordinate-lattice inclusion is proper and discrete. -/
theorem cavityGridLattice_tendsto_cofinite_cocompact (q : ℕ) (ell : ℝ) :
    Tendsto (fun g : CavityGridLattice (Fin q) ell ↦ fun i ↦ (g i : ℝ))
      cofinite (cocompact (Fin q → ℝ)) := by
  have he : IsClosedEmbedding
      (fun g : CavityGridLattice (Fin q) ell ↦ fun i ↦ (g i : ℝ)) :=
    Topology.IsClosedEmbedding.piMap fun _ : Fin q ↦
      (AddSubgroup.isClosed_of_discrete (H := AddSubgroup.zmultiples ell)).isClosedEmbedding_subtypeVal
  exact tendsto_cofinite_cocompact_of_discrete he.tendsto_cocompact

/-- The closed envelope of one literal existing half-open spatial grid cell. -/
def originalClosedSpatialGridCell (q : ℕ) (ell : ℝ) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) : Set (Fin q → ℝ) :=
  {x | x - (g +ᵥ u) ∈ Icc 0 (fun _ ↦ ell)}

/-- The closed complete-edge envelope retains both original endpoint clocks freely. -/
def originalClosedCompleteGridCell (q : ℕ) (ell : ℝ) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) : Set (LegalMarkedPhysicalEdge q) :=
  {e | e.1.1 ∈ originalClosedSpatialGridCell q ell u g ∧
    e.2.1 ∈ originalClosedSpatialGridCell q ell u g}

/-- Closed spatial cell envelopes are actually closed. -/
theorem isClosed_originalClosedSpatialGridCell (q : ℕ) (ell : ℝ) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) :
    IsClosed (originalClosedSpatialGridCell q ell u g) :=
  isClosed_Icc.preimage (continuous_id.sub continuous_const)

/-- Closed complete-cell envelopes are actually closed in the full original edge space. -/
theorem isClosed_originalClosedCompleteGridCell (q : ℕ) (ell : ℝ) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) :
    IsClosed (originalClosedCompleteGridCell q ell u g) :=
  ((isClosed_originalClosedSpatialGridCell q ell u g).preimage continuous_fst.fst).inter
    ((isClosed_originalClosedSpatialGridCell q ell u g).preimage continuous_snd.fst)

/-- Every original half-open complete cell is in this same closed envelope. -/
theorem originalCompleteGridCell_subset_closed (q : ℕ) (ell : ℝ) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) :
    originalCompleteGridCell q ell u g ⊆ originalClosedCompleteGridCell q ell u g := by
  have hsp : cavityGridCube (Fin q) ell (g +ᵥ u) ⊆
      originalClosedSpatialGridCell q ell u g := by
    intro x hx
    exact ⟨fun i ↦ (hx i (mem_univ i)).1.le, fun i ↦ (hx i (mem_univ i)).2⟩
  exact fun e he ↦ ⟨hsp he.1, hsp he.2⟩

/-- Closed spatial cell translates form a locally finite family by the actual
proper discrete inclusion of the existing coordinate lattice. -/
theorem locallyFinite_originalClosedSpatialGridCell (q : ℕ) (ell : ℝ)
    (u : Fin q → ℝ) : LocallyFinite (originalClosedSpatialGridCell q ell u) := by
  intro x
  let B : Set (Fin q → ℝ) :=
    (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦ p.1 - u - p.2) ''
      (Metric.closedBall x 1 ×ˢ Icc (0 : Fin q → ℝ) (fun _ ↦ ell))
  have hB : IsCompact B := ((isCompact_closedBall x 1).prod isCompact_Icc).image
    ((continuous_fst.sub continuous_const).sub continuous_snd)
  have hfinite : {g : CavityGridLattice (Fin q) ell |
      (fun i ↦ (g i : ℝ)) ∈ B}.Finite :=
    (tendsto_cofinite_cocompact_iff.mp (cavityGridLattice_tendsto_cofinite_cocompact q ell)) B hB
  refine ⟨Metric.ball x 1, Metric.isOpen_ball.mem_nhds (by simp), hfinite.subset ?_⟩
  intro g hg
  obtain ⟨y, hycell, hyball⟩ := hg
  refine ⟨(y, y - (g +ᵥ u)), ⟨Metric.ball_subset_closedBall hyball, hycell⟩, ?_⟩
  ext i
  change y i - u i - (y i - ((g i : ℝ) + u i)) = (g i : ℝ)
  ring

/-- The complete original edge-cell envelopes are locally finite independently
of the original scalar-clock laws or displacement moments. -/
theorem locallyFinite_originalClosedCompleteGridCell (q : ℕ) (ell : ℝ)
    (u : Fin q → ℝ) : LocallyFinite (originalClosedCompleteGridCell q ell u) := by
  intro e
  obtain ⟨U, hU, hfin⟩ := locallyFinite_originalClosedSpatialGridCell q ell u e.1.1
  let V : Set (LegalMarkedPhysicalEdge q) := {f | f.1.1 ∈ U}
  have hV : V ∈ 𝓝 e :=
    ((continuous_fst.comp continuous_fst : Continuous
      (fun f : LegalMarkedPhysicalEdge q ↦ f.1.1)).tendsto e).eventually hU
  refine ⟨V, hV, hfin.subset ?_⟩
  intro g hg
  obtain ⟨f, hfg, hfV⟩ := hg
  exact ⟨f.1.1, hfg.1, hfV⟩

/-- No complete-cell piece gains a support point outside its original closed envelope. -/
theorem support_originalCompleteGridPiece_subset_closed (q : ℕ) (ell : ℝ)
    (u : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell)
    (s : LegalMarkedOptimalInputScene q) :
    (originalCompleteGridPiece q ell g (s, u) : Measure (LegalMarkedPhysicalEdge q)).support ⊆
      originalClosedCompleteGridCell q ell u g := by
  have hc : closure (originalCompleteGridCell q ell u g) ⊆
      originalClosedCompleteGridCell q ell u g :=
    (isClosed_originalClosedCompleteGridCell q ell u g).closure_subset_iff.mpr
      (originalCompleteGridCell_subset_closed q ell u g)
  exact (Measure.support_restrict_subset (μ := (s.1.1 : Measure (LegalMarkedPhysicalEdge q)))
    (s := originalCompleteGridCell q ell u g)).trans (inter_subset_left.trans hc)

/-- Crossed partners of two complete edges are in that very same original cell. -/
theorem crossed_mem_originalCompleteGridCell (q : ℕ) (ell : ℝ) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) {e f : LegalMarkedPhysicalEdge q}
    (he : e ∈ originalCompleteGridCell q ell u g) (hf : f ∈ originalCompleteGridCell q ell u g) :
    (e.1, f.2) ∈ originalCompleteGridCell q ell u g ∧
      (f.1, e.2) ∈ originalCompleteGridCell q ell u g :=
  ⟨⟨he.1, hf.2⟩, ⟨hf.1, he.2⟩⟩

/-- The actual two-edge exchange stays within the same closed complete cell,
so infinitely many disjoint cell exchanges remain locally finite. -/
theorem support_originalCompleteGridPiece_swap_subset_closed (q : ℕ) (ell : ℝ)
    (u : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell)
    (s : LegalMarkedOptimalInputScene q) {e f : LegalMarkedPhysicalEdge q}
    (he : e ∈ originalCompleteGridCell q ell u g) (hf : f ∈ originalCompleteGridCell q ell u g) :
    (originalTwoEdgeSwapPlan (originalCompleteGridPiece q ell g (s, u)) e f :
      Measure (LegalMarkedPhysicalEdge q)).support ⊆ originalClosedCompleteGridCell q ell u g := by
  intro x hx
  rcases support_originalTwoEdgeSwapPlan_subset
    (originalCompleteGridPiece q ell g (s, u)) e f hx with hx | hx
  · exact support_originalCompleteGridPiece_subset_closed q ell u g s hx
  · have hcross := crossed_mem_originalCompleteGridCell q ell u g he hf
    rcases hx with hx | hx
    · exact originalCompleteGridCell_subset_closed q ell u g
        (mem_singleton_iff.mp hx ▸ hcross.1)
    · exact originalCompleteGridCell_subset_closed q ell u g
        (mem_singleton_iff.mp hx ▸ hcross.2)

end OTSelector.Reconstruction
