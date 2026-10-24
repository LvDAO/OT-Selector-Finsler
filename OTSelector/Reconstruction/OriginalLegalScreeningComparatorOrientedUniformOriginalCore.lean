import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedOriginalCore
import OTSelector.Finite.MatchingReserveDeletion
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockOriginalDeletedCountsKept

/-! One actual original retained core supports every original reserve deletion at once. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators Topology ContDiff Classical
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

/-- The true retained plan determines one original-index legal core before
any reserve deletion is selected. Every original reserve label is free, and
all deletion-dependent unused counting laws hold for this same core. -/
theorem ae_exists_originalFullIndex_orientedPathRetainedCore_uniform_deletions
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
    ∀ (m n ks kt : ℕ)
      (x : Fin m → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (y : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (vs : Fin ks → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (vt : Fin kt → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (rs : Fin ks ↪ Fin m) (rt : Fin kt ↪ Fin n),
      Injective x → Injective y → (∀ j, x (rs j) = vs j) → (∀ j, y (rt j) = vt j) →
      (∑ i, Measure.dirac (x i)) =
        (legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}+
          ∑ j, Measure.dirac (vs j) →
      (∑ i, Measure.dirac (y i)) =
        (legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2*R)}+
          ∑ j, Measure.dirac (vt j) →
    ∀ cost : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) → ℝ,
    ∃ σ : OTSelector.PartialMatching m n,
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) σ ∧
      (originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
        ∑ e ∈ σ.edges, Measure.dirac (x e.1,y e.2) ∧
      Integrable cost (originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) ∧
      (∫ e, cost e ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) = σ.cost (fun i j ↦ cost (x i,y j)) ∧
      Finset.univ.map rs ⊆ σ.freeRows ∧ Finset.univ.map rt ⊆ σ.freeCols ∧
      ∀ (Ds : Finset (Fin ks)) (Dt : Finset (Fin kt)),
        Ds.map rs ⊆ σ.freeRows ∧ Dt.map rt ⊆ σ.freeCols ∧
        let U := σ.freeRows \ Ds.map rs
        let V := σ.freeCols \ Dt.map rt
        U ⊆ σ.freeRows ∧ V ⊆ σ.freeCols ∧
        (∑ i ∈ U, Measure.dirac (x i)) =
          (originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
            (originalCenteredPhysicalCubeRegion b (2*R)) scene :
            Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst+
              ∑ j ∈ Finset.univ \ Ds, Measure.dirac (vs j) ∧
        (∑ i ∈ V, Measure.dirac (y i)) =
          (originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
            (originalCenteredPhysicalCubeRegion b (2*R)) scene :
            Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd+
              ∑ j ∈ Finset.univ \ Dt, Measure.dirac (vt j) := by
  filter_upwards [D.ae_exists_originalFullIndex_orientedPathRetainedCore hF hw Q b hell hR]
    with scene hcore
  intro m n ks kt x y vs vt rs rt hx hy hrs hrt hs ht cost
  obtain ⟨σ,hσ,hplan,_,hI,hcost,hfreeS,hfreeT,hwindowS,hwindowT⟩ :=
    hcore m n x y (∑ j,Measure.dirac (vs j)) (∑ j,Measure.dirac (vt j)) hx hy hs ht cost
  have hsf : Finset.univ.map rs ⊆ σ.freeRows :=
    (originalReserveEmbedding_deleted_subset_atomIndices x vs rs hx hrs Finset.univ).trans hfreeS
  have htf : Finset.univ.map rt ⊆ σ.freeCols :=
    (originalReserveEmbedding_deleted_subset_atomIndices y vt rt hy hrt Finset.univ).trans hfreeT
  refine ⟨σ,hσ,hplan,hI,hcost,hsf,htf,?_⟩
  intro Ds Dt
  have hds : Ds.map rs ⊆ σ.freeRows :=
    (originalReserveEmbedding_deleted_subset_atomIndices x vs rs hx hrs Ds).trans hfreeS
  have hdt : Dt.map rt ⊆ σ.freeCols :=
    (originalReserveEmbedding_deleted_subset_atomIndices y vt rt hy hrt Dt).trans hfreeT
  have hsrem := sourceUnusedOriginalLaw_after_reserveDeletion σ x vs rs hrs hsf _ hwindowS Ds
  have htrem := targetUnusedOriginalLaw_after_reserveDeletion σ y vt rt hrt htf _ hwindowT Dt
  exact ⟨hds,hdt,hsrem.1,htrem.1,hsrem.2,htrem.2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
