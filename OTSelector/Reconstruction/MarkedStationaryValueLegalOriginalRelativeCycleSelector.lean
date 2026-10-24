import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalJointSceneReroot
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCompleteGridCells
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCycleLocalPatch

/-! # One Borel original-edge selector viewed from each actual cell base -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

/-- A single reference-cell selection rule. All fields are constructed below
from the existing actual integer atom code. -/
structure OriginalOriginCycleSelector (q : ℕ) (c : LegalMarkedPhysicalEdge q → ℝ)
    (ell ε : ℝ) where
  pair : LegalMarkedOptimalInputScene q → LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q
  measurable_pair : Measurable pair
  active : Set (LegalMarkedOptimalInputScene q)
  measurable_active : MeasurableSet active
  certificate : ∀ s ∈ active, originalLegalCycleCertificate c
    (originalCompleteGridCell q ell 0 0) ε (pair s)
  support : ∀ s, IsFullOriginalInputMatching q s → s ∈ active →
    (pair s).1 ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support ∧
      (pair s).2 ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support
  active_of_witness : ∀ s, IsFullOriginalInputMatching q s →
    (∃ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
      ∃ f ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        originalLegalCycleCertificate c (originalCompleteGridCell q ell 0 0) ε (e, f)) →
    s ∈ active

/-- A Borel first witness supplies the actual reference-cell rule, without
adding a selection hypothesis to the original transport problem. -/
theorem exists_originalOriginCycleSelector (q : ℕ)
    (c : LegalMarkedPhysicalEdge q → ℝ) (hc : Measurable c) (ell ε : ℝ) :
    Nonempty (OriginalOriginCycleSelector q c ell ε) := by
  let R : LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q → Prop :=
    originalLegalCycleCertificate c (originalCompleteGridCell q ell 0 0) ε
  have hR : MeasurableSet {p | R p} := measurableSet_originalLegalCycleCertificate c hc
    (measurableSet_originalCompleteGridCell q ell 0 0) ε
  obtain ⟨choose, hchoose, hspec⟩ := exists_measurable_originalCountingPair_selection
    (0 : LegalMarkedPhysicalEdge q)
    (fun s : LegalMarkedOptimalInputScene q ↦ s.1.1) measurable_fst.fst
    (fun _ ↦ R) (hR.preimage measurable_snd)
  let A : Set (LegalMarkedOptimalInputScene q) := {s | ∃ n,
    originalCountingPairWitness (0 : LegalMarkedPhysicalEdge q) s.1.1 R n}
  have hA : MeasurableSet A := measurableSet_exists_originalCountingPairWitness _
    (fun s : LegalMarkedOptimalInputScene q ↦ s.1.1) measurable_fst.fst
    (fun _ ↦ R) (hR.preimage measurable_snd)
  refine ⟨⟨choose, hchoose, A ∩ {s | R (choose s)},
    hA.inter (hR.preimage hchoose), fun s hs ↦ hs.2, ?_, ?_⟩⟩
  · intro s hs ha
    have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
    have hsel := hspec s hcount
      ((exists_originalCountingPairWitness_iff _ s.1.1 hcount R).mp ha.1)
    exact ⟨hsel.1, hsel.2.1⟩
  · intro s hs hw
    have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
    exact ⟨(exists_originalCountingPairWitness_iff _ s.1.1 hcount R).mpr hw,
      (hspec s hcount hw).2.2⟩

variable {q : ℕ} {c : LegalMarkedPhysicalEdge q → ℝ} {ell ε : ℝ}

/-- The fixed original rule observes the whole scene from the actual cell base. -/
def OriginalOriginCycleSelector.relativeActive (S : OriginalOriginCycleSelector q c ell ε) :
    Set ((Fin q → ℝ) × LegalMarkedOptimalInputScene q) :=
  {p | legalMarkedInputSceneReroot q p.1 p.2 ∈ S.active}

theorem OriginalOriginCycleSelector.measurable_relativeActive
    (S : OriginalOriginCycleSelector q c ell ε) : MeasurableSet S.relativeActive :=
  S.measurable_active.preimage (measurable_legalMarkedInputSceneReroot_joint q)

/-- Selected endpoints are moved back to their literal original coordinates. -/
def OriginalOriginCycleSelector.relativePair (S : OriginalOriginCycleSelector q c ell ε)
    (p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q) :
    LegalMarkedPhysicalEdge q × LegalMarkedPhysicalEdge q :=
  let ef := S.pair (legalMarkedInputSceneReroot q p.1 p.2)
  (physicalSceneEdgeReroot (-p.1) ef.1, physicalSceneEdgeReroot (-p.1) ef.2)

theorem OriginalOriginCycleSelector.measurable_relativePair
    (S : OriginalOriginCycleSelector q c ell ε) : Measurable S.relativePair := by
  have hp := S.measurable_pair.comp (measurable_legalMarkedInputSceneReroot_joint q)
  have h1 : Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      physicalSceneEdgeReroot (-p.1) (S.pair (legalMarkedInputSceneReroot q p.1 p.2)).1) := by
    change Measurable ((fun p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q ↦
      physicalSceneEdgeReroot p.1 p.2) ∘
        (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
          (-p.1, (S.pair (legalMarkedInputSceneReroot q p.1 p.2)).1)))
    exact continuous_physicalSceneEdgeReroot_uncurry.measurable.comp
      (measurable_fst.neg.prodMk hp.fst)
  have h2 : Measurable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      physicalSceneEdgeReroot (-p.1) (S.pair (legalMarkedInputSceneReroot q p.1 p.2)).2) := by
    change Measurable ((fun p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q ↦
      physicalSceneEdgeReroot p.1 p.2) ∘
        (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
          (-p.1, (S.pair (legalMarkedInputSceneReroot q p.1 p.2)).2)))
    exact continuous_physicalSceneEdgeReroot_uncurry.measurable.comp
      (measurable_fst.neg.prodMk hp.snd)
  exact h1.prodMk h2

/-- The success event sees the identical relative scene after physical reroot. -/
theorem OriginalOriginCycleSelector.relativeActive_reroot
    (S : OriginalOriginCycleSelector q c ell ε) (b v : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) :
    (b - v, legalMarkedInputSceneReroot q v s) ∈ S.relativeActive ↔
      (b, s) ∈ S.relativeActive := by
  change legalMarkedInputSceneReroot q (b - v) (legalMarkedInputSceneReroot q v s)
    ∈ S.active ↔ legalMarkedInputSceneReroot q b s ∈ S.active
  rw [legalMarkedInputSceneReroot_relative]

/-- The same selected original pair transforms covariantly, even though its
shell code itself need not be invariant under translation. -/
theorem OriginalOriginCycleSelector.relativePair_reroot
    (S : OriginalOriginCycleSelector q c ell ε) (b v : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) :
    S.relativePair (b - v, legalMarkedInputSceneReroot q v s) =
      (physicalSceneEdgeReroot v (S.relativePair (b, s)).1,
        physicalSceneEdgeReroot v (S.relativePair (b, s)).2) := by
  simp only [relativePair, legalMarkedInputSceneReroot_relative]
  apply Prod.ext <;> apply Prod.ext <;> apply Prod.ext
  all_goals try rfl
  all_goals change _ - -(b - v) = (_ - -b) - v
  all_goals abel

@[simp] theorem physicalSceneEdgeReroot_symm (v : Fin q → ℝ) :
    (physicalSceneEdgeReroot v).symm = physicalSceneEdgeReroot (-v) := by
  simp only [physicalSceneEdgeReroot, physicalScenePointReroot,
    Homeomorph.prodCongr_symm, Homeomorph.addRight_symm, Homeomorph.refl_symm]

/-- Every successful selected relative edge is actually occupied in the same
original full matching. -/
theorem OriginalOriginCycleSelector.relativePair_support
    (S : OriginalOriginCycleSelector q c ell ε) (b : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) (hs : IsFullOriginalInputMatching q s)
    (ha : (b, s) ∈ S.relativeActive) :
    (S.relativePair (b, s)).1 ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support ∧
      (S.relativePair (b, s)).2 ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support := by
  have hsel := S.support _ (hs.reroot b) ha
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  constructor
  · have hback := (mem_support_mapHomeomorph_iff_of_legalCounting
      (0 : LegalMarkedPhysicalEdge q) (physicalSceneEdgeReroot b) s.1.1 hcount _).mp hsel.1
    simpa only [physicalSceneEdgeReroot_symm, relativePair] using hback
  · have hback := (mem_support_mapHomeomorph_iff_of_legalCounting
      (0 : LegalMarkedPhysicalEdge q) (physicalSceneEdgeReroot b) s.1.1 hcount _).mp hsel.2
    simpa only [physicalSceneEdgeReroot_symm, relativePair] using hback

/-- Moving an origin-cell edge back places both unchanged endpoints in the
literal cell based at the chosen root. -/
theorem originalCompleteGridCell_reroot_neg_iff (q : ℕ) (ell : ℝ)
    (b : Fin q → ℝ) (e : LegalMarkedPhysicalEdge q) :
    physicalSceneEdgeReroot (-b) e ∈ originalCompleteGridCell q ell b 0 ↔
      e ∈ originalCompleteGridCell q ell 0 0 := by
  change ((e.1.1 - -b) - ((0 : CavityGridLattice (Fin q) ell) +ᵥ b) ∈ cavityGridPhaseCell (Fin q) ell ∧
    (e.2.1 - -b) - ((0 : CavityGridLattice (Fin q) ell) +ᵥ b) ∈ cavityGridPhaseCell (Fin q) ell) ↔
      (e.1.1 - ((0 : CavityGridLattice (Fin q) ell) +ᵥ (0 : Fin q → ℝ)) ∈ cavityGridPhaseCell (Fin q) ell ∧
        e.2.1 - ((0 : CavityGridLattice (Fin q) ell) +ᵥ (0 : Fin q → ℝ)) ∈ cavityGridPhaseCell (Fin q) ell)
  simp only [zero_vadd, sub_neg_eq_add, add_sub_cancel_right, sub_zero]

/-- A successful relative rule certifies the same exact original weighted
cost saving in the actual cell, with both crossed clocks still legal. -/
theorem OriginalOriginCycleSelector.relativePair_certificate
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin g t) ell ε)
    (b : Fin q → ℝ) (s : LegalMarkedOptimalInputScene q)
    (ha : (b, s) ∈ S.relativeActive) :
    originalLegalCycleCertificate (originalWeightedEdgeCost kin g t)
      (originalCompleteGridCell q ell b 0) ε (S.relativePair (b, s)) := by
  let ef := S.pair (legalMarkedInputSceneReroot q b s)
  have hcert := S.certificate (legalMarkedInputSceneReroot q b s) ha
  change originalLegalCycleCertificate _ _ ε ef at hcert
  rcases hcert with ⟨hne, he, hf, hcross1, hcross2, hsaving⟩
  refine ⟨?_, (originalCompleteGridCell_reroot_neg_iff q ell b ef.1).mpr he,
    (originalCompleteGridCell_reroot_neg_iff q ell b ef.2).mpr hf,
    hcross1, hcross2, ?_⟩
  · exact fun h ↦ hne ((physicalSceneEdgeReroot (-b)).injective h)
  · change ε ≤ originalWeightedEdgeCost kin g t (physicalSceneEdgeReroot (-b) ef.1) +
      originalWeightedEdgeCost kin g t (physicalSceneEdgeReroot (-b) ef.2) -
      originalWeightedEdgeCost kin g t (physicalSceneEdgeReroot (-b) (ef.1.1, ef.2.2)) -
      originalWeightedEdgeCost kin g t (physicalSceneEdgeReroot (-b) (ef.2.1, ef.1.2))
    simpa only [originalWeightedEdgeCost_reroot] using hsaving

end OTSelector.Reconstruction
