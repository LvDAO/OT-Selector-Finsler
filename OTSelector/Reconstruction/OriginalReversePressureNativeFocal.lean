import OTSelector.Reconstruction.OriginalReversePressureNearFrameCandidate
import OTSelector.Reconstruction.OriginalReversePressureInnerCubeLimit
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapePressureLimit
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeNearCubeGeometry

/-! Genuine native-cube focal pressure lies below every original weighted stationary candidate. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The native original focal pressure is bounded by the signed value of every
genuine weighted candidate. Actual minimizers, clock couplings, grids, current
frames, finite legal repairs, Poisson expectations and all vanishing reserves
and spatial holes are constructed internally. The weighted candidate needs no
Euclidean second moment, and no comparison or pressure limit is assumed. -/
theorem OriginalSeedConditionalMoments.originalFocalPressure_le_same_candidate
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {densityμ densityν : M → ℝ} {v : M → E → ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀ x, 0 ≤ densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀ x, 0 ≤ densityν x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ,E) old).target, 0 ≤ v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ ↦ x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ G)
    (hgc : ContinuousOn (Function.uncurry g) {p | p.1-S.level ∈ Ioo D.lo D.hi ∧
      p.2-S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2}) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    let : IsProbabilityMeasure μ := D.support.source.probability
    let : IsProbabilityMeasure ν := D.support.target.probability
    limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker)
      id id μ ν (D.originalFocalKinetic gap) g R τ) ≤ Q.value τ := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let b₀ := EuclideanSpace.basisFun (Fin q) ℝ
  have hG : 0 ≤ G := (abs_nonneg (g 0 0)).trans (hgb 0 0)
  obtain ⟨π,hprob,hπ,hforward⟩ := Q.exists_originalForwardClockCoupling
  let : IsProbabilityMeasure π := hprob
  have horder : ∀ᵐ p ∂π, p.1 ≤ p.2 := hforward.mono (fun _ h ↦ h.le)
  obtain ⟨p₀,hlim₀,_hconc,_hlip⟩ := D.exists_originalFocalFrame_pressure_limit hF hw hq
    hgap hbounds π hπ horder hG hg hgb b₀
  have hnative (t : ℝ) : Tendsto (fun R ↦ legalMarkedScalePressure q id id μ ν
      (D.originalFocalKinetic gap) g R t) atTop (𝓝 (p₀ t)) := by
    have hk₀ : originalScreeningFrameKinetic b₀ (D.originalFocalKinetic gap) =
        D.originalFocalKinetic gap := by
      funext a d v
      simp only [b₀,originalScreeningFrameKinetic,orthonormalPhysicalCubeMap_basisFun]
    simpa only [hk₀] using hlim₀ t
  change limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure q id id μ ν
    (D.originalFocalKinetic gap) g R τ) ≤ Q.value τ
  rw [(hnative τ).limUnder_eq]
  let I : Set ℝ := μ.support ∪ ν.support
  have hIcompact : IsCompact I := hbounds.source_compact.union hbounds.target_compact
  obtain ⟨bins⟩ := exists_finiteScalarBins hIcompact hgap
  have hsrc : ∀ᵐ p ∂π, p.1 ∈ μ.support :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact μ.support_mem_ae)
  have htgt : ∀ᵐ p ∂π, p.2 ∈ ν.support :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact ν.support_mem_ae)
  have hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I :=
    (hsrc.and htgt).mono (fun _ h ↦ ⟨Or.inl h.1,Or.inr h.2⟩)
  obtain ⟨C,hC,hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  let A := C*(q : ℝ)*dyadicMatchingConstant q*((bins.count+1 : ℕ) : ℝ)^(2/(q : ℝ))
  have hscale : Tendsto (fun δ : ℝ ↦ 1/(1+(q : ℝ)*δ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hd : Tendsto (fun δ : ℝ ↦ δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hh : Tendsto (fun δ : ℝ ↦ 1+(q : ℝ)*δ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa only [mul_zero,add_zero] using (hd.const_mul (q : ℝ)).const_add (1 : ℝ)
    simpa only [one_div,inv_one] using hh.inv₀ one_ne_zero
  apply originalPressure_le_sameCandidate_of_vanishing_innerCube (q := q) (by dsimp [q]; omega)
    (C := A) (L := |τ| * G) hscale
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  obtain ⟨b,hnear,p₁,hlim₁,hvalue⟩ := D.exists_original_nearFrame_pressure_le_candidate hF hw hq
    cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap hg hgb hgc τ Q b₀ hδ
  let s : ℝ := 1/(1+(q : ℝ)*δ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1/2) :=
    originalOrientedShapeNearFrame_cube_subset b hδ.le (fun i ↦ (hnear i).le)
  have hshape := bins.originalOrientedShape_pressure_limit_le hgap hIcompact.measurableSet
    π μ ν hπ hI (hbounds.ae_clock_gap_of_coupling hπ horder) hbounds hq hC hG
    (D.measurable_originalFocalKinetic hF hw gap)
    (D.originalFocalKinetic_nonneg hF hw hgap) hkb
    (fun a d c _ x ↦ D.originalFocalKinetic_homogeneous gap a d c x)
    hg hgb τ b hs hsub (p₀ τ) p₁ (hnative τ) hlim₁
  change p₀ τ ≤ s^q*Q.value τ+A*(1-s^q)^(1-2/(q : ℝ))+|τ| * G*(1-s^q)
  apply hshape.trans
  change s^q*p₁+A*(1-s^q)^(1-2/(q : ℝ))+|τ| * G*(1-s^q) ≤
    s^q*Q.value τ+A*(1-s^q)^(1-2/(q : ℝ))+|τ| * G*(1-s^q)
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hvalue (pow_nonneg hs.le q)) le_rfl) le_rfl

end OTSelector.Reconstruction
