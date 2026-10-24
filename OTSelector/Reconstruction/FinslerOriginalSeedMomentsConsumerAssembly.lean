import OTSelector.Reconstruction.FinslerOriginalSeedMomentsConsumer

/-!
# Seed-moments consumer with existentially selected cut data

`FinslerOriginalSeedMomentsConsumer` produces, at one label and from a.e. CDF
dominance only, the marked-stationary witness: seed label membership, clock
support bounds, the seed conditional-moments datum, the weighted-stationary
minimizer and a nonempty bounded second-moment class.

The common-scale consumer
`ae_original_minimizer_commonScale_finalUnconditional` additionally needs the
seed-dependent per-label truncation/cut data (`T`, `cut`, `h`, `ell`, ...) with
its analytic hypotheses.  This file packages exactly that tuple as a structure
(so no large consumer statement is ever written out for the data), gives the
consumer bounds for any supplied tuple as a definition with an inferred type,
and states the composed consumer theorem with only the witness data plus the
supplied tuple as inputs.

Remaining gap: the analytic cut-data hypotheses (`hsmall`, `hR`, `hRLip`,
`hbound`, `hKthreshold`, `hsingle`, ...) have no producer in the repository from
the capstone witness, so the tuple is an explicit input (`hprov`); the exact
missing projection is recorded in the report.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold Metric Topology
  OTSelector.Geometry ContinuousFinslerNorm OTSelector.PointProcess
  OTSelector.PointProcess.StationaryForwardMatching OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology

noncomputable section

set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.defProp false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The seed-dependent per-label truncation/cut data required by the
marked-stationary common-scale consumer, bundled with its analytic hypotheses.
The tuple is over a fixed datum, clock pair and matching, so it can be chosen
after the witness has been selected. -/
structure MarkedStationaryConsumerData
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν)
    {gap diameter : ℝ} {G : ℝ} {g : ℝ → ℝ → ℝ} (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) where
  /-- The compliance-transport matrix. -/
  T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ
  invertible : Invertible T
  cut : ℝ
  h : ℝ
  ell : ℝ
  a : ℝ
  hcut : cut ∈ Ioo D.lo D.hi
  hh : 0 < h
  ha : 0 ≤ a
  hclockRange : ∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi
  hsmall : ∀ r ∈ Icc (0 : ℝ) 1,
    ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ *
      Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ)
  ρ : ℝ
  A : ℝ
  hA : 0 ≤ A
  hR : ∀ r ∈ Icc (0 : ℝ) 1,
    ‖originalNormalizedClockMobility S w T (cut + S.level) ell r‖ ≤ ρ
  hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
    ‖originalNormalizedClockMobility S w T (cut + S.level) ell r -
      originalNormalizedClockMobility S w T (cut + S.level) ell r'‖ ≤ A * |r - r'|
  η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞
  f : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞
  hη : Measurable η
  hf : Measurable f
  hclock : ∀ m c, f (m, c) ≠ 0 →
    ∃ r ∈ Icc (0 : ℝ) 1, c = cut + S.level + ell * r
  hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a
  hmask : ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker), ∀ c,
    f ((physicalPairAnchor e).2, c) ≠ 0 →
      e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h
  B : ℝ
  K : ℝ
  hB : 0 ≤ B
  hK : 0 ≤ K
  hbound : ∀ e ∈ legalMarkedCompletePathContributors (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f,
    legalMarkedCompletePathEdgeTraffic (finrank ℝ S.covector.ker)
      (fun z ↦ originalSeedPathOffset S w z.2 z.1) η f e ≤ ENNReal.ofReal B
  hηfinite : (∫⁻ x, η x ∂(volume : Measure
    (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ (⊤ : ℝ≥0∞)
  hffinite : (∫⁻ m, ∫⁻ c : ℝ, f (m, c) ∂volume
    ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞)
  hpfinite : (∫⁻ m, ∫⁻ c : ℝ,
    ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m) * f (m, c) ∂volume
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (⊤ : ℝ≥0∞)
  hKthreshold :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let radius := max (2 * (a + ρ * b)) (b + 2 * (L : ℝ) * (a + ρ * b))
    D.normalizedSourcePhaseCurveCountThreshold T cut radius ≤ K
  hsingle : ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
    ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
    (∫⁻ c : ℝ, η (x + originalSeedPathOffset S w c m) * f (m, c) ∂volume) ≤
      ENNReal.ofReal B

/-- The marked-stationary common-scale bound for a supplied cut-data tuple.  The
consumer statement is not restated: the type is inferred from the consumer
application, so only the data tuple is mentioned. -/
noncomputable def markedStationaryBoundOfData
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker)
      μ ν (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    (C : MarkedStationaryConsumerData (D := D) (gap := gap) (diameter := diameter)
      (G := G) (g := g) (t := t) (Q := Q)) := by
  haveI : Invertible C.T := C.invertible
  exact D.ae_original_minimizer_commonScale_finalUnconditional hF hw hgap hbounds
    C.T hg hgb t Q hmin C.hcut C.hh C.ha C.hclockRange C.hsmall
    (ρ := C.ρ) (A := C.A) C.hA C.hR C.hRLip
    (η := C.η) (f := C.f) C.hη C.hf C.hclock C.hηwindow C.hmask
    (B := C.B) C.hB (K := C.K) C.hK C.hbound C.hηfinite C.hffinite C.hpfinite
    C.hKthreshold C.hsingle
/-- Witness selection plus supplied cut data: from the capstone inputs and a
provider of the seed-dependent truncation/cut data tuple (the exact missing
projection, since the consumer's analytic cut hypotheses have no producer from
the capstone witness), the full marked-stationary data tuple exists at one
label.  Applying `markedStationaryBoundOfData` to this tuple then yields the
marked-stationary common-scale consumer bound. -/
theorem exists_markedStationaryConsumerData_of_cdf_dominance
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {kappa : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {eta0 eta1 : Measure M} [IsFiniteMeasure eta0] [IsFiniteMeasure eta1]
    {rho0 rho1 : M → ℝ} {v : M → E → ℝ}
    [IsProbabilityMeasure lambda]
    (hsupported : PopulationSupportedComparisonLaw P a kappa lambda eta0 eta1
      rho0 rho1 v)
    (hF : F.IsSmoothStronglyConvex)
    (hrho0 : Continuous rho0) (hrho1 : Continuous rho1)
    (hrho0nonneg : ∀ x, 0 ≤ rho0 x) (hrho1nonneg : ∀ x, 0 ≤ rho1 x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x)
    {A : Set M} (hA : IsCompact A)
    (hatomA : ∀ᵐ z ∂lambda, NullSingletonClass (condDistrib u a eta0 z) ∧
      IsCompact (condDistrib u a eta0 z).support ∧
      (condDistrib u a eta0 z).support ⊆ u '' A)
    {delta diameter : ℝ} (hdelta : 0 < delta)
    (hboundsAE : ∀ᵐ z ∂lambda,
      ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter)
    (hdom : ∀ᵐ z ∂lambda, ∀ s : ℝ,
      cdf (condDistrib u a eta1 z) s ≤ cdf (condDistrib u a eta0 z) s)
    (hq : ∀ j, 4 < finrank ℝ (P j).seed.covector.ker)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ s t, |g s t| ≤ G)
    (hgc : Continuous (Function.uncurry g)) (t : ℝ)
    (hprov : ∀ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker)
        (datum : OriginalSeedConditionalMoments (P j).seed w
          (condDistrib u a eta0 z) (condDistrib u a eta1 z))
        (Qmin : LegalWeightedStationaryPoissonMatching
          (finrank ℝ (P j).seed.covector.ker) (condDistrib u a eta0 z)
          (condDistrib u a eta1 z) (datum.originalFocalKinetic delta) g)
        (hw : w ∈ (P j).seed.labels)
        (hbnd : ConditionalClockSupportBounds (condDistrib u a eta0 z)
          (condDistrib u a eta1 z) delta diameter),
        (∀ P' : LegalWeightedStationaryPoissonMatching
          (finrank ℝ (P j).seed.covector.ker) (condDistrib u a eta0 z)
          (condDistrib u a eta1 z) (datum.originalFocalKinetic delta) g,
          Qmin.value t ≤ P'.value t) →
        MarkedStationaryConsumerData (D := datum) (gap := delta)
          (diameter := diameter) (G := G) (g := g) (t := t) (Q := Qmin)) :
    ∃ (z : Z) (j : ℕ) (w : (P j).seed.covector.ker)
      (datum : OriginalSeedConditionalMoments (P j).seed w
        (condDistrib u a eta0 z) (condDistrib u a eta1 z))
      (Qmin : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker) (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) (datum.originalFocalKinetic delta) g)
      (hw : w ∈ (P j).seed.labels)
      (hbnd : ConditionalClockSupportBounds (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) delta diameter),
      (∀ P' : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker) (condDistrib u a eta0 z)
        (condDistrib u a eta1 z) (datum.originalFocalKinetic delta) g,
        Qmin.value t ≤ P'.value t) ∧
      Nonempty (MarkedStationaryConsumerData (D := datum) (gap := delta)
        (diameter := diameter) (G := G) (g := g) (t := t) (Q := Qmin)) := by
  obtain ⟨z, j, w, datum, hw, hbnd, ⟨Qmin, hmin⟩, _Qprobe, _Bnd, _hBnd0, _hclass⟩ :=
    exists_minimizer_witness_of_cdf_dominance hsupported hF hrho0 hrho1 hrho0nonneg
      hrho1nonneg hv hv0 hA hatomA hdelta hboundsAE hdom hq g hg hgb hgc t
  exact ⟨z, j, w, datum, Qmin, hw, hbnd, hmin,
    ⟨hprov z j w datum Qmin hw hbnd hmin⟩⟩

end OTSelector.Reconstruction

end