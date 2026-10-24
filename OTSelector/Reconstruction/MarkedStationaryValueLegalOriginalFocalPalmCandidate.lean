import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalFullScene
import OTSelector.Reconstruction.MarkedStationaryValueLegalFocalSignedPalmEnergy
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-!
# The actual original focal pressure produces a weighted Poisson Palm matching

The candidate is the same canonical original legal finite-optimum weak limit.
All original colored inputs are used in a genuine integer one-to-one matching;
its true full-displacement probability Palm has the two original clock laws
and finite original weighted energy. Focal endpoint degeneration is allowed.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff CompactlySupported Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
local instance markedStationaryValueLegalOriginalFocalPalmCandidateInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalOriginalFocalPalmCandidatePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Original conditional data produce a genuine full original Poisson
stationary matching with signed weighted Palm value at most actual legal
pressure. No finite unweighted displacement moment is used or asserted. -/
theorem exists_original_focal_weightedStationaryPoissonMatching_energy_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} (hG : 0 ≤ G) {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (hgc : ContinuousOn (Function.uncurry g)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2}) :
    let _ : IsProbabilityMeasure μ := D.support.source.probability
    let _ : IsProbabilityMeasure ν := D.support.target.probability
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id μ ν
        (D.originalFocalKinetic gap) g R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p ∧
      ∀ t : ℝ, ∃ M : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
          (D.originalFocalKinetic gap) g,
        M.value t ≤ p t ∧
        ∃ (L : ℕ → ℝ) (hL : ∀ k, 0 < L k), Tendsto L atTop atTop ∧
          Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw (finrank ℝ S.covector.ker) μ ν
            (D.originalFocalKinetic gap) (D.measurable_originalFocalKinetic hF hw gap) g hg t
            (L k) (hL k)) atTop (𝓝 M.law) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let kin := D.originalFocalKinetic gap
  have hk := D.measurable_originalFocalKinetic hF hw gap
  have hq0 : 0 < q := by dsimp [q]; omega
  obtain ⟨C, hC, hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  have hsep : ∀ᵐ p ∂μ.prod ν, gap ≤ |p.2 - p.1| := by
    filter_upwards [ae_fst_of_ae μ.support_mem_ae, ae_snd_of_ae ν.support_mem_ae] with p hp hq
    simpa only [Real.dist_eq, abs_sub_comm] using hbounds.separated p.1 hp p.2 hq
  obtain ⟨p, hp, hc, hl, hscene⟩ := D.exists_stationary_original_focal_fullInput_scene
    hF hw hq hgap hbounds π hπ horder hG hg hgb
  refine ⟨p, hp, hc, hl, fun t ↦ ?_⟩
  obtain ⟨L, hL, hlarge, Q, φ, hφ, hwk, hstat, hfull, hinput⟩ := hscene t
  have hlargeφ := hlarge.comp hφ.tendsto_atTop
  let J : Set ℝ := {a | a - S.level ∈ Ioo D.lo D.hi}
  have hJ : IsOpen J := isOpen_Ioo.preimage (continuous_id.sub (continuous_const (y := (S.level : ℝ))))
  let A : Set ℝ := J ∩ μ.support
  let B : Set ℝ := J ∩ ν.support
  have hA : MeasurableSet A := hJ.measurableSet.inter μ.isClosed_support.measurableSet
  have hB : MeasurableSet B := hJ.measurableSet.inter ν.isClosed_support.measurableSet
  have hα : μ Aᶜ = 0 := ae_iff.mp (D.support.source.ae_open.and μ.support_mem_ae)
  have hβ : ν Bᶜ = 0 := ae_iff.mp (D.support.target.ae_open.and ν.support_mem_ae)
  let O : Set (ℝ × ℝ) := {p | p.1 ∈ J ∧ p.2 ∈ J ∧ p.1 < p.2}
  have hO : IsOpen O := (hJ.preimage continuous_fst).inter
    ((hJ.preimage continuous_snd).inter (isOpen_lt continuous_fst continuous_snd))
  have henergy := integrable_signed_cubePalm_le_legalMarkedPressure_limit_of_interior q hq0 μ ν
    hC hG hk (D.originalFocalKinetic_nonneg hF hw hgap) hkb
    (fun a b c _ v ↦ D.originalFocalKinetic_homogeneous gap a b c v) hg hgb t (p t) (hp t)
    hA hB hα hβ hO (originalSeedPairCoefficient S w) (D.continuousOn_pair_coefficient_interior hF hw)
    (fun p hp ↦ (D.pair_compliance_posDef hF hw hp.1 hp.2.1 hp.2.2).2.posSemidef)
    (fun _ ha _ hb hab ↦ ⟨ha.1, hb.1, hab⟩)
    (fun _ ha _ hb hab v ↦ D.originalFocalKinetic_eq_of_original_support hbounds ha hb hab v)
    hgc hgap hsep (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hlargeφ hwk hstat hfull
  have hPalm := probability_cubePalm_of_legalMarkedInputSceneLaw_tendsto q μ ν kin hk g hg t
    (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hlargeφ hwk hstat hfull
  have hmatching := ae_isFullOriginalInputMatching_of_legalMarkedInputSceneLaw_tendsto
    q hq0 μ ν kin hk g hg t (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hlargeφ hwk hfull
  have hforward : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
    filter_upwards [ae_support_clockGap_of_legalMarkedInputSceneLaw_tendsto
      q hq0 μ ν kin hk g hg t (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hwk hsep] with s hs
    intro e he
    have h := hs e he
    linarith
  let M : LegalWeightedStationaryPoissonMatching q μ ν kin g :=
    { law := Q
      stationary := hstat
      full_matching := hmatching
      forward := hforward
      input_laplace := hinput
      palm_probability := hPalm.1
      source_clock := hPalm.2.1
      target_clock := hPalm.2.2
      kinetic_integrable := henergy.1
      probe_integrable := henergy.2.1 }
  exact ⟨M, henergy.2.2, (fun k ↦ L (φ k)), (fun k ↦ hL (φ k)), hlargeφ, hwk⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
