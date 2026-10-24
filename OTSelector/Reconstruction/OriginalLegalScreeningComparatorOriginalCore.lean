import OTSelector.Reconstruction.OriginalWindowPortConservation
import OTSelector.Reconstruction.OriginalLegalWeightedReserveCompletion

/-! The actual path-length retained plan is extracted in the unchanged complete
original input arrays. Original reserve indices remain free and the port laws
are the exact remaining original endpoint measures. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Actual integer retention, actual full-scene clock legality and the true
window conservation construct one original-index core. The original full arrays
may include all reserve points: their zero/one reserve-origin indices are proved
unused on both sides, and both exact remaining-measure identities are internal.
No core, selected-point law or residual-capacity conclusion is an input. -/
theorem ae_exists_originalFullIndex_pathRetainedCore
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2*ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
    ∀ (m n : ℕ)
      (x : Fin m → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (y : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (ρs ρt : Measure (LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))),
      Injective x → Injective y →
      (∑ i, Measure.dirac (x i)) =
        (legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R}+ρs →
      (∑ j, Measure.dirac (y j)) =
        (legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R}+ρt →
    ∀ cost : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) → ℝ,
    ∃ σ : OTSelector.PartialMatching m n,
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) σ ∧
      (originalPathRetainedPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
        ∑ e ∈ σ.edges, Measure.dirac (x e.1, y e.2) ∧
      (originalPathRetainedPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ =
        (σ.card : ℝ≥0∞) ∧
      Integrable cost (originalPathRetainedPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) ∧
      (∫ e, cost e ∂(originalPathRetainedPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) =
        σ.cost (fun i j ↦ cost (x i,y j)) ∧
      originalReserveAtomIndices ρs x ⊆ σ.freeRows ∧
      originalReserveAtomIndices ρt y ⊆ σ.freeCols ∧
      (∑ i, Measure.dirac (x i)) =
        (∑ e ∈ σ.edges, Measure.dirac (x e.1))+
          (originalPathSourcePortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst+ρs ∧
      (∑ j, Measure.dirac (y j)) =
        (∑ e ∈ σ.edges, Measure.dirac (y e.2))+
          (originalPathTargetPortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd+ρt := by
  filter_upwards [Q.full_matching,
    D.ae_originalPathRetainedPlan_legal_inner_paths hF hw Q hell hR,
    D.ae_original_windows_eq_retained_add_ports hF hw Q hell hR]
      with scene hfull hlegal hwindow
  intro m n x y ρs ρt hx hy hsource htarget cost
  let core := originalPathRetainedPlan S w R ell scene
  let μs := (legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R}
  let μt := (legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R}
  have hcs : (core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ≤ μs := by
    change (originalPathRetainedPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ≤
      (legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R}
    rw [hwindow.1]
    exact Measure.le_add_right le_rfl
  have hct : (core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd ≤ μt := by
    change (originalPathRetainedPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd ≤
      (legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R}
    rw [hwindow.2]
    exact Measure.le_add_right le_rfl
  have hsourceFull : (core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst ≤ ∑ i, Measure.dirac (x i) := by
    rw [hsource]
    exact hcs.trans (Measure.le_add_right le_rfl)
  have htargetFull : (core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd ≤ ∑ j, Measure.dirac (y j) := by
    rw [htarget]
    exact hct.trans (Measure.le_add_right le_rfl)
  have hc := ((isLegalSimpleCountingMeasure_iff _ _).mp
    (hfull.simple_originalPathRetainedPlan (S := S) (w := w) R ell)).1
  have hsupp : ∀ᵐ e ∂(core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      e ∈ (core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support :=
    Measure.support_mem_ae
  have hforward : ∀ᵐ e ∂(core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))), e.1.2 < e.2.2 :=
    hsupp.mono (fun e he ↦ (hlegal e he).2.2.1)
  obtain ⟨σ, hσ, hmeasure, hmass, hI, hcost⟩ :=
    exists_originalIndex_legal_partialMatching_cost_of_integer_plan
      (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) core hc x y hx hy hsourceFull htargetFull
      (fun a b ↦ a.2 < b.2) hforward cost
  have hs : (core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst =
      ∑ e ∈ σ.edges, Measure.dirac (x e.1) := by
    rw [hmeasure]
    simp only [Measure.fst, Measure.map_finset_sum measurable_fst.aemeasurable, Measure.map_dirac]
  have ht : (core : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd =
      ∑ e ∈ σ.edges, Measure.dirac (y e.2) := by
    rw [hmeasure]
    simp only [Measure.snd, Measure.map_finset_sum measurable_snd.aemeasurable, Measure.map_dirac]
  have hds : Disjoint σ.rows (originalReserveAtomIndices ρs x) :=
    originalReserveAtomIndices_disjoint_used σ.edges Prod.fst x hx μs ρs hsource.symm (hs ▸ hcs)
  have hdt : Disjoint σ.cols (originalReserveAtomIndices ρt y) :=
    originalReserveAtomIndices_disjoint_used σ.edges Prod.snd y hy μt ρt htarget.symm (ht ▸ hct)
  refine ⟨σ, hσ, hmeasure, hmass, hI, hcost, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hu ↦ Finset.disjoint_left.mp hds hu hi⟩
  · intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hu ↦ Finset.disjoint_left.mp hdt hu hj⟩
  · rw [hsource, hwindow.1, hs]
  · rw [htarget, hwindow.2, ht]
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
