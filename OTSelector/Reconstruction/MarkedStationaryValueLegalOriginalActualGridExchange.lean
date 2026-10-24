import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalRelativeCycleSelector
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCompleteGridLocalFiniteness
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCellExchangeGluing
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalGridExchangeCovariance

/-! # The literal actual complete-cell competitor on the unchanged input -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

/-- View the whole original scene from this literal coarse-cell base. -/
def originalGridRelativeObservation (q : ℕ) (ell : ℝ)
    (g : CavityGridLattice (Fin q) ell)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ)) :
    (Fin q → ℝ) × LegalMarkedOptimalInputScene q := (g +ᵥ p.2, p.1)

theorem measurable_originalGridRelativeObservation (q : ℕ) (ell : ℝ)
    (g : CavityGridLattice (Fin q) ell) : Measurable (originalGridRelativeObservation q ell g) := by
  change Measurable (fun p : LegalMarkedOptimalInputScene q × (Fin q → ℝ) ↦
    ((fun i ↦ (g i : ℝ)) + p.2, p.1))
  exact (measurable_const.add measurable_snd).prodMk measurable_fst

variable {q : ℕ} {ell ε : ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {probe : ℝ → ℝ → ℝ} {t : ℝ}

/-- Exchange only the selected two original complete-cell edges, retaining
the entire remaining original cell measure. -/
def originalExchangedGridPiece
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (g : CavityGridLattice (Fin q) ell)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ)) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  let o := originalGridRelativeObservation q ell g p
  if o ∈ S.relativeActive then
    originalTwoEdgeSwapPlan (originalCompleteGridPiece q ell g p)
      (S.relativePair o).1 (S.relativePair o).2
  else originalCompleteGridPiece q ell g p

theorem measurable_originalExchangedGridPiece
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (g : CavityGridLattice (Fin q) ell) : Measurable (originalExchangedGridPiece S g) := by
  have ho := measurable_originalGridRelativeObservation q ell g
  have hp := S.measurable_relativePair.comp ho
  apply Measurable.ite (S.measurable_relativeActive.preimage ho)
  · change Measurable ((fun p : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) ×
      (LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q) ↦
      originalTwoEdgeSwapPlan p.1 p.2.1 p.2.2) ∘
      (fun p : LegalMarkedOptimalInputScene q × (Fin q → ℝ) ↦
        (originalCompleteGridPiece q ell g p,
          S.relativePair (originalGridRelativeObservation q ell g p))))
    exact (measurable_originalTwoEdgeSwapPlan q).comp
      ((measurable_originalCompleteGridPiece q ell g).prodMk hp)
  · exact measurable_originalCompleteGridPiece q ell g

/-- The transported reference certificate concerns the literal actual grid cell. -/
theorem originalExchangedGridPiece_certificate
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (g : CavityGridLattice (Fin q) ell)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ))
    (ha : originalGridRelativeObservation q ell g p ∈ S.relativeActive) :
    originalLegalCycleCertificate (originalWeightedEdgeCost kin probe t)
      (originalCompleteGridCell q ell p.2 g) ε
      (S.relativePair (originalGridRelativeObservation q ell g p)) := by
  simpa only [originalCompleteGridCell, zero_vadd, originalGridRelativeObservation] using
    S.relativePair_certificate kin probe t (g +ᵥ p.2) p.1 ha

/-- Every exchanged cell stays in the same locally finite closed spatial
envelope, including on scenes outside the full-matching event. -/
theorem support_originalExchangedGridPiece_subset_closed
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (g : CavityGridLattice (Fin q) ell)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ)) :
    (originalExchangedGridPiece S g p : Measure (LegalMarkedPhysicalEdge q)).support ⊆
      originalClosedCompleteGridCell q ell p.2 g := by
  classical
  dsimp only [originalExchangedGridPiece]
  split_ifs with ha
  · have hc := originalExchangedGridPiece_certificate S g p ha
    exact support_originalCompleteGridPiece_swap_subset_closed q ell p.2 g p.1
      hc.2.1 hc.2.2.1
  · exact support_originalCompleteGridPiece_subset_closed q ell p.2 g p.1

/-- The literal countable competitor is locally finite; no new clock gap or
moment assumption is used to define it. -/
theorem originalExchangedGridPiece_sum_finiteOnCompacts
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ)) :
    IsFiniteMeasureOnCompacts
      (Measure.sum (fun g ↦ (originalExchangedGridPiece S g p : Measure (LegalMarkedPhysicalEdge q)))) :=
  originalPlanSum_finiteOnCompacts_of_locallyFinite _ _
    (locallyFinite_originalClosedCompleteGridCell q ell p.2)
    (fun g ↦ support_originalExchangedGridPiece_subset_closed S g p)

/-- The exchanged pieces are actual integer measures on every original full scene. -/
theorem IsFullOriginalInputMatching.counting_exchangedGridPiece
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell) :
    IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) (originalExchangedGridPiece S g (s, u)) := by
  classical
  dsimp only [originalExchangedGridPiece]
  split_ifs
  · exact isLegalCountingMeasure_originalTwoEdgeSwapPlan _
      (hs.counting_completeGridPiece ell u g) _ _
  · exact hs.counting_completeGridPiece ell u g

/-- Every successful cell exchanges two actual unit atoms and preserves both
whole endpoint marginals of its literal original restriction. -/
theorem IsFullOriginalInputMatching.exchangedGridPiece_marginals
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell) :
    (originalExchangedGridPiece S g (s, u) : Measure (LegalMarkedPhysicalEdge q)).fst =
      (originalCompleteGridPiece q ell g (s, u) : Measure (LegalMarkedPhysicalEdge q)).fst ∧
    (originalExchangedGridPiece S g (s, u) : Measure (LegalMarkedPhysicalEdge q)).snd =
      (originalCompleteGridPiece q ell g (s, u) : Measure (LegalMarkedPhysicalEdge q)).snd := by
  classical
  dsimp only [originalExchangedGridPiece]
  split_ifs with ha
  · have hcert := originalExchangedGridPiece_certificate S g (s, u) ha
    have hsupp := S.relativePair_support (g +ᵥ u) s hs ha
    exact originalTwoEdgeSwapPlan_marginals_of_unit_atoms _ hcert.1
      (hs.completeGridPiece_singleton_eq_one ell u g hsupp.1 hcert.2.1)
      (hs.completeGridPiece_singleton_eq_one ell u g hsupp.2 hcert.2.2.1)
  · exact ⟨rfl, rfl⟩

/-- All original edges crossing the grid remain literally unchanged. -/
def originalCrossingGridPiece (q : ℕ) (ell : ℝ)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ)) :
    LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨(p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
    (⋃ g, originalCompleteGridCell q ell p.2 g)ᶜ, inferInstance⟩

theorem measurable_originalCrossingGridPiece (q : ℕ) (ell : ℝ) :
    Measurable (originalCrossingGridPiece q ell) := by
  let U : Set ((LegalMarkedOptimalInputScene q × (Fin q → ℝ)) ×
      LegalMarkedPhysicalEdge q) := {p | p.2 ∉ ⋃ g, originalCompleteGridCell q ell p.1.2 g}
  have hU : MeasurableSet U := by
    have hB (g : CavityGridLattice (Fin q) ell) :
        MeasurableSet {p : (LegalMarkedOptimalInputScene q × (Fin q → ℝ)) ×
          LegalMarkedPhysicalEdge q | p.2 ∈ originalCompleteGridCell q ell p.1.2 g} :=
      (measurableSet_originalCompleteGridCell_joint q ell g).preimage
        (measurable_fst.snd.prodMk measurable_snd)
    convert (MeasurableSet.iUnion hB).compl using 1
    ext p
    simp only [U, mem_compl_iff, mem_iUnion, mem_ofPred_eq]
  exact measurable_originalParameterizedRestriction (fun p ↦ p.1.1.1)
    measurable_fst.fst.fst U hU

/-- The actual exchanged complete cells plus all unchanged crossing edges. -/
def originalGridExchangeScene
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ)) : LegalMarkedOptimalInputScene q :=
  originalCellGluedScene p.1 (originalCrossingGridPiece q ell p)
    (fun g ↦ originalExchangedGridPiece S g p)
    (originalExchangedGridPiece_sum_finiteOnCompacts S p)

@[simp] theorem originalGridExchangeScene_input
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (p : LegalMarkedOptimalInputScene q × (Fin q → ℝ)) :
    (originalGridExchangeScene S p).2 = p.1.2 := rfl

theorem measurable_originalGridExchangeScene
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε) :
    Measurable (originalGridExchangeScene S) := by
  have hm := measurable_originalCellGluedPlan
    (originalCrossingGridPiece q ell) (measurable_originalCrossingGridPiece q ell)
    (fun p g ↦ originalExchangedGridPiece S g p)
    (measurable_originalExchangedGridPiece S)
    (originalExchangedGridPiece_sum_finiteOnCompacts S)
  exact (hm.prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd

/-- The concrete countable exchange is a full one-to-one matching of every
unchanged original colored input atom. -/
theorem IsFullOriginalInputMatching.gridExchange
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (hell : 0 < ell)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u : Fin q → ℝ) : IsFullOriginalInputMatching q (originalGridExchangeScene S (s, u)) := by
  apply hs.cellGlue (originalCrossingGridPiece q ell (s, u))
    (fun g ↦ originalCompleteGridPiece q ell g (s, u))
    (fun g ↦ originalExchangedGridPiece S g (s, u))
    (originalExchangedGridPiece_sum_finiteOnCompacts S (s, u))
  · exact measure_eq_crossing_add_completeGridPieces q hell u _
  · exact isLegalCountingMeasure_restrict _ s.1.1
      ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1 _
  · exact hs.counting_exchangedGridPiece S u
  · exact hs.exchangedGridPiece_marginals S u

/-- Every literal exchanged cell keeps strict forward legality at all occupied
original and crossed edges. -/
theorem forward_originalExchangedGridPiece
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (s : LegalMarkedOptimalInputScene q)
    (hf : ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    (u : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell) :
    ∀ e ∈ (originalExchangedGridPiece S g (s, u) :
      Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
  have hfcell : ∀ e ∈ (originalCompleteGridPiece q ell g (s, u) :
      Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
    intro e he
    exact hf e ((Measure.support_restrict_subset
      (μ := (s.1.1 : Measure (LegalMarkedPhysicalEdge q)))
      (s := originalCompleteGridCell q ell u g)) he).2
  classical
  dsimp only [originalExchangedGridPiece]
  split_ifs with ha
  · have hc := originalExchangedGridPiece_certificate S g (s, u) ha
    intro e he
    have hm := support_originalTwoEdgeSwapPlan_subset (originalCompleteGridPiece q ell g (s, u))
      _ _ he
    rcases hm with h | h
    · exact hfcell e h
    · rcases h with h | h
      · exact (mem_singleton_iff.mp h) ▸ hc.2.2.2.1
      · exact (mem_singleton_iff.mp h) ▸ hc.2.2.2.2.1
  · exact hfcell

/-- The concrete global competitor retains strict original-clock legality. -/
theorem IsFullOriginalInputMatching.forward_gridExchange
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (hf : ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    (hell : 0 < ell)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u : Fin q → ℝ) : ∀ e ∈ ((originalGridExchangeScene S (s, u)).1.1 :
      Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
  apply forward_originalCellGluedScene s (originalCrossingGridPiece q ell (s, u))
    (fun g ↦ originalExchangedGridPiece S g (s, u))
    (originalExchangedGridPiece_sum_finiteOnCompacts S (s, u))
    ((isLegalSimpleCountingMeasure_iff _ _).mp (hs.gridExchange hell S u).simple_edges).1
  · intro e he
    exact hf e ((Measure.support_restrict_subset
      (μ := (s.1.1 : Measure (LegalMarkedPhysicalEdge q)))
      (s := (⋃ g, originalCompleteGridCell q ell u g)ᶜ)) he).2
  · exact forward_originalExchangedGridPiece S s hf u

end OTSelector.Reconstruction
