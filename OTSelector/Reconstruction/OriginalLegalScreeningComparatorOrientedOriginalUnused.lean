import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedOriginalCore
import OTSelector.Finite.MatchingReserveDeletion

/-! Real original reserve deletion identifies the exact unused original indices
and counting laws after the actual path-length retained core. -/
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

/-- The same-frame core and any actual original reserve deletion identify
exact remaining original endpoint laws. No prescribed global cardinality is
required: blockwise deletions may leave different global color totals. The
unchanged retained plan, legal core and signed cost are produced internally. -/
theorem ae_exists_originalFullIndex_orientedPathRetainedCore_after_reserveDeletion
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell)
    (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) :
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
    ∀ (Ds : Finset (Fin ks)) (Dt : Finset (Fin kt)), 
    ∀ cost : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) → ℝ,
    ∃ σ : OTSelector.PartialMatching m n,
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) σ ∧
      (originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
        ∑ e ∈ σ.edges, Measure.dirac (x e.1,y e.2) ∧
      Integrable cost (originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) ∧
      (∫ e, cost e ∂(originalStageRestrictedPathPlan (originalOrientedPathLengthRetained S w b R ell) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) =
        σ.cost (fun i j ↦ cost (x i,y j)) ∧
      let U := σ.freeRows \ Ds.map rs
      let V := σ.freeCols \ Dt.map rt
      U ⊆ σ.freeRows ∧ V ⊆ σ.freeCols ∧
      (∑ i ∈ U, Measure.dirac (x i)) =
        (originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell) (originalCenteredPhysicalCubeRegion b (2*R)) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst+
          ∑ j ∈ Finset.univ \ Ds, Measure.dirac (vs j) ∧
      (∑ i ∈ V, Measure.dirac (y i)) =
        (originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell) (originalCenteredPhysicalCubeRegion b (2*R)) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd+
          ∑ j ∈ Finset.univ \ Dt, Measure.dirac (vt j) := by
  filter_upwards [D.ae_exists_originalFullIndex_orientedPathRetainedCore hF hw Q b hell hR] with scene hcore
  intro m n ks kt x y vs vt rs rt hx hy hxs hyt hsource htarget Ds Dt cost
  obtain ⟨σ, hσ, hplan, _, hI, hcost, hfreeS, hfreeT, hwindowS, hwindowT⟩ :=
    hcore m n x y (∑ j, Measure.dirac (vs j)) (∑ j, Measure.dirac (vt j)) hx hy hsource htarget cost
  have hvs : Injective vs := by
    intro i j hij
    apply rs.injective
    apply hx
    rw [hxs, hxs]
    exact hij
  have hvt : Injective vt := by
    intro i j hij
    apply rt.injective
    apply hy
    rw [hyt, hyt]
    exact hij
  have hunitS (j : Fin ks) : (∑ k, Measure.dirac (vs k)) {x (rs j)} = 1 := by
    rw [hxs]
    simp [Measure.finsetSum_apply, Measure.dirac_apply', Pi.single_apply, hvs.eq_iff]
  have hunitT (j : Fin kt) : (∑ k, Measure.dirac (vt k)) {y (rt j)} = 1 := by
    rw [hyt]
    simp [Measure.finsetSum_apply, Measure.dirac_apply', Pi.single_apply, hvt.eq_iff]
  have hrs : Finset.univ.map rs ⊆ σ.freeRows := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact hfreeS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hunitS j⟩)
  have hrt : Finset.univ.map rt ⊆ σ.freeCols := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact hfreeT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hunitT j⟩)
  have hremS := sourceUnusedOriginalLaw_after_reserveDeletion σ x vs rs hxs hrs _ hwindowS Ds
  have hremT := targetUnusedOriginalLaw_after_reserveDeletion σ y vt rt hyt hrt _ hwindowT Dt
  exact ⟨σ, hσ, hplan, hI, hcost, hremS.1, hremT.1, hremS.2, hremT.2⟩
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
