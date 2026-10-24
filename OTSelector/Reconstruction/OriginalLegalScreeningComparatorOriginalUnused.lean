import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOriginalCore
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

/-- The actual complete-array readout, original reserve embedding and exact
full color-excess deletion produce balanced unused original subarrays of the
right completion cardinality. Both remaining counting laws are exactly the
literal original ports plus undeleted original reserves. The core and its signed
cost are extracted internally; no capacity or remaining-law premise is supplied. -/
theorem ae_exists_originalFullIndex_pathRetainedCore_after_excessDeletion
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2*ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
    ∀ (m n ks kt : ℕ)
      (x : Fin m → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (y : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (vs : Fin ks → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (vt : Fin kt → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
      (rs : Fin ks ↪ Fin m) (rt : Fin kt ↪ Fin n),
      Injective x → Injective y → (∀ j, x (rs j) = vs j) → (∀ j, y (rt j) = vt j) →
      (∑ i, Measure.dirac (x i)) =
        (legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ haarRootCube _ R}+
          ∑ j, Measure.dirac (vs j) →
      (∑ i, Measure.dirac (y i)) =
        (legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ haarRootCube _ R}+
          ∑ j, Measure.dirac (vt j) →
    ∀ (Ds : Finset (Fin ks)) (Dt : Finset (Fin kt)), Ds.card = m-n → Dt.card = n-m →
    ∀ cost : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) → ℝ,
    ∃ σ : OTSelector.PartialMatching m n,
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2)) σ ∧
      (originalPathRetainedPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
        ∑ e ∈ σ.edges, Measure.dirac (x e.1,y e.2) ∧
      Integrable cost (originalPathRetainedPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) ∧
      (∫ e, cost e ∂(originalPathRetainedPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) =
        σ.cost (fun i j ↦ cost (x i,y j)) ∧
      let U := σ.freeRows \ Ds.map rs
      let V := σ.freeCols \ Dt.map rt
      U ⊆ σ.freeRows ∧ V ⊆ σ.freeCols ∧ σ.card+U.card = min m n ∧ U.card = V.card ∧
      (∑ i ∈ U, Measure.dirac (x i)) =
        (originalPathSourcePortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst+
          ∑ j ∈ Finset.univ \ Ds, Measure.dirac (vs j) ∧
      (∑ i ∈ V, Measure.dirac (y i)) =
        (originalPathTargetPortPlan S w R ell scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd+
          ∑ j ∈ Finset.univ \ Dt, Measure.dirac (vt j) := by
  filter_upwards [D.ae_exists_originalFullIndex_pathRetainedCore hF hw Q hell hR] with scene hcore
  intro m n ks kt x y vs vt rs rt hx hy hxs hyt hsource htarget Ds Dt hDs hDt cost
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
  have hds : Ds.map rs ⊆ σ.freeRows := (Finset.map_subset_map.mpr (Finset.subset_univ Ds)).trans hrs
  have hdt : Dt.map rt ⊆ σ.freeCols := (Finset.map_subset_map.mpr (Finset.subset_univ Dt)).trans hrt
  have hdscard : (Ds.map rs).card = m-n := by simpa only [Finset.card_map] using hDs
  have hdtcard : (Dt.map rt).card = n-m := by simpa only [Finset.card_map] using hDt
  have hremS := sourceUnusedOriginalLaw_after_reserveDeletion σ x vs rs hxs hrs _ hwindowS Ds
  have hremT := targetUnusedOriginalLaw_after_reserveDeletion σ y vt rt hyt hrt _ hwindowT Dt
  exact ⟨σ, hσ, hplan, hI, hcost, hremS.1, hremT.1,
    (sourceDeletedUnused_count_spec σ _ hds hdscard).2,
    excessDeletedUnused_card_eq σ _ _ hds hdt hdscard hdtcard, hremS.2, hremT.2⟩
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
