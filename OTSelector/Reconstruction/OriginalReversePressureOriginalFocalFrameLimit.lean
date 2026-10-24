import OTSelector.Reconstruction.OriginalLegalScreeningPressureFrame
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalFullScene

/-! The actual original focal model produces its pressure limit in every fixed physical frame. -/
open Set Function MeasureTheory Filter Topology Module Manifold
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The same original focal coefficient and genuine forward clock population
produce a real-scale pressure limit in any fixed orthonormal frame. Endpoint
degeneration is retained; no coercivity, second moment or pressure limit is an input. -/
theorem exists_originalFocalFrame_pressure_limit
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} (hG : 0 ≤ G) {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker)
        id id μ ν (originalScreeningFrameKinetic b (D.originalFocalKinetic gap)) g R t)
        atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G,hG⟩ p := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let I : Set ℝ := μ.support ∪ ν.support
  have hI : IsCompact I := hbounds.source_compact.union hbounds.target_compact
  obtain ⟨bins⟩ := exists_finiteScalarBins hI hgap
  have hsrc : ∀ᵐ p ∂π, p.1 ∈ μ.support :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact μ.support_mem_ae)
  have htgt : ∀ᵐ p ∂π, p.2 ∈ ν.support :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact ν.support_mem_ae)
  have hcarry : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I :=
    (hsrc.and htgt).mono (fun _ h ↦ ⟨Or.inl h.1,Or.inr h.2⟩)
  have hsep : ∀ᵐ p ∂μ.prod ν, gap ≤ |p.2-p.1| := by
    filter_upwards [ae_fst_of_ae μ.support_mem_ae,ae_snd_of_ae ν.support_mem_ae]
      with p hs ht
    simpa only [Real.dist_eq,abs_sub_comm] using hbounds.separated p.1 hs p.2 ht
  obtain ⟨C,hC,hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  exact exists_legalMarkedScalePressure_limit_of_scalarBins bins hgap hI.measurableSet
    id id measurable_id measurable_id π μ ν hπ hcarry
    (hbounds.ae_clock_gap_of_coupling hπ horder) hsep (finrank ℝ S.covector.ker) hq hC hG
    (measurable_originalScreeningFrameKinetic b (D.measurable_originalFocalKinetic hF hw gap))
    (fun a c v ↦ D.originalFocalKinetic_nonneg hF hw hgap a c _)
    (originalScreeningFrameKinetic_quadratic_bound b hkb)
    (originalScreeningFrameKinetic_homogeneous b
      (fun a c d _ v ↦ D.originalFocalKinetic_homogeneous gap a c d v)) hg hgb

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
