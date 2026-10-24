import OTSelector.Reconstruction.FinslerOriginalEndgameActualWired
import OTSelector.Reconstruction.FinslerOriginalEndgameReadoutDerivative
import OTSelector.Reconstruction.FinslerOriginalFocalValueLimit
import OTSelector.Reconstruction.FinslerOriginalUpperPoolDuality
import OTSelector.Reconstruction.FinslerOriginalFrozenLowerDomination
import OTSelector.Reconstruction.FinslerOriginalIntrinsicFrozenEstimate
import OTSelector.Reconstruction.FinslerOriginalLegalPressureValueEquality

/-! # Consolidated paper-facing endgame data and the selector theorem

This module is the single consolidated paper-facing surface of the general
Finsler selector.  It produces the endgame data |FinslerPaperEndgameData| at the
derived calibrated potential |paperCalibratedPotential| with every newly landed
producer wired in, and states the selector theorem at that data.

## What is produced

* |consolidatedStationaryDatum|: the actual stationary pressure datum family
  (the |stationaryForwardDatum| of the weighted stationary matching class, i.e.
  the |C_w|/|C_2| decomposition of main.tex, definition
  general-gluing-two-classes);
* |paperEndgameData_actual_consolidated|: the paper endgame data
  |FinslerPaperEndgameData| at |paperCalibratedPotential|, with
  - |hC| (frozen Campbell readout, F15) from P1 + P2 via
    |frozenCampbellReadout_of_populationFocalValueLimit_and_attainment|
    (|FinslerOriginalFocalValueLimit|);
  - |hU| (upper stationary readout, F18) from the lower-bound paper identity and
    the reverse bound via |actualUpperReadout_of_lowerBound_and_reverseBound|
    (|FinslerOriginalUpperPoolDuality|);
  - |hprob| (unshifted lower probability, F12) from the paper's bare domination
    |hbaredom| via |finalProbLowerData_of_frozen_domination|
    (|FinslerOriginalFrozenLowerDomination|);
  - |hscreen| (screening) proved here from
    |weightedClass_eq_secondMomentClass_of_uniform_elliptic|
    (|FinslerOriginalLegalPressureValueEquality|), screening |Q| by itself;
  - the F13 upper bundle at the intrinsic interface
    (|physicalWeightedLocalizationFamily_of_intrinsicPointwiseBound| composed with
    |endgameUpperFields_of_weightedLocalization|,
    |FinslerOriginalIntrinsicFrozenEstimate|), using the sample-dependent kinetic bound
    and the eventual freezing estimate;
  - the geometric hypotheses from |PaperGeometricSeedDatum| via
    |paperGeometricHypotheses_of_seedDatum|
    (|FinslerOriginalPaperGeometricBundleActual|).
* |existsUnique_general_finsler_selector_at_derivedPotential_consolidated|: the
  paper selector theorem at the derived potential consuming
  |paperEndgameData_actual_consolidated|. Its readout derivative follows from the
  lower probability bound, upper expectation bound and value identification via
  |finslerReadoutTiltDerivative_of_paperEndgameData|.

## Residual typed inputs (`main.tex` lines from the producer module docstrings)

Each row lists binders of |paperEndgameData_actual_consolidated| that are not
derived from other binders, their type, the paper provenance, and whether a
producer exists elsewhere in the repository.  The exact type of every binder is
printed in its declaration below; the type column gives the named interface.

| input | type | paper provenance | producer elsewhere? |
| --- | --- | --- | --- |
| |hF|, |hcomplete|, |hdim|, |m|, |ωM|, |ρ₀|, |ρ₁|, |v|, |hv|, |hvnonneg|, |hvolume|, |hA|, |hB|, |hAB|, |hμA|, |hνB| and the population probability instances | standing smooth-strongly-convex Finsler and population hypotheses | main.tex standing hypotheses of the general Finsler selector (no single display) | no: these are the hypotheses consumed by |paperCalibratedPotential| (|FinslerOriginalEndgameActualWired|) |
| |Ω|, |sample|, |X|, |Y|, |hX|, |hY|, |hXi|, |hYi|, |hXlaw|, |hYlaw|, |hXY| | semi-discrete sampling model | main.tex population/sampling model | no: probabilistic model data |
| |Seed|, |a|, |κ|, |lambda|, |ha|, |hinj|, |[IsFiniteMeasure lambda]|, |[CountablySeparated (ℚ → M)]| | |F.CalibratedSeedWindow| family, regular-domain embedding, seed-covector family measures | seed and atlas definitions of the paper | no: |CalibratedSeedWindow| is a definition; the embedding |(a, u)| is the paper's regular-domain parametrization |
| |seedDatum| | |PaperGeometricSeedDatum F u (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)| | paper geometric seed hypotheses | structure only (|FinslerOriginalPaperGeometricBundleActual:67|); no term is constructed in the repo, |paperGeometricHypotheses_of_seedDatum| (:111) consumes it |
| |η₀|, |η₁|, |ρl₀|, |ρl₁|, |vf|, |bf|, |Good|, |r|, |δ|, |loss|, |Dl| | |PopulationLocalPressureCore Seed a κ lambda η₀ η₁ ρl₀ ρl₁ vf bf Good r δ loss| | population local pressure core of the lower lane | interface only, no term |
| |εt|, |T| | |Dl.TaylorTiles εt| | Taylor tiles of the lower lane | no |
| |α|, |β|, |Ag|, |fg|, |C|, |hA_meas|, |hA_nonneg|, |hA_bound|, |hf_meas|, |hfG|, |competitor|, |competitor2|, |hcompetitor|, |hcompetitor_K|, |hcompetitor2|, |hcompetitor2_K| | weighted stationary functional and two competitor classes | main.tex definition general-gluing-two-classes | no |
| |coef|, |probeFam|, |Mst|, |q|, |hM|, |hAcoef|, |hprobe|, |hprobe_bound| | per-piece coefficient, probe and stationary-matching families, tilt scale | per-root Campbell data of the paper | no |
| |hP1| | |PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q| | main.tex general-focal-value-equality (approx. 11029-11052), general-gluing-integrated-pressures (11382-11399), general-finsler-pressure-limit (11565-11582), highd-measurable-pressure (5442-5460) | no: single typed paper input |
| |hP2| | |FrozenAttainment Seed a κ lambda α β coef probeFam Mst q| | same chain: frozen attainment / proposition general-gluing-conditional-readout | no: single typed paper input |
| |c|, |hc|, |hA_low| | uniform ellipticity |0 < c|, |c ≤ Ag φ x y| | paper interior-collar / elliptic case (|FinslerOriginalLegalPressureValueEquality|: prop:general-finite-path-screening, thm:general-focal-value-equality) | no: the class equality producer turns it into the screening proved here |
| |frozenCost|, |hId|, |hbaredom|, |hfrozen_int| | frozen cost family, |RootedTileCampbellMeanIdentification ... T.Index|, unshifted support bound, integrability | |hbaredom|: main.tex 5596-5606 (high-dimensional lower bound) and 7917-7941 (general gluing), general-gluing-finite-domination after the |B_t| cancellation; |hId|: tile Campbell mean identification (conjunct (iv) of the lower lane) | |hfrozen_int|: producer |hprobFrozenInputs_tileScale_of_geometricLane| (|FinslerOriginalFrozenScaleIdentification:268|) for |hprobFrozenCostFamily| under the geometric-lane tile scale; |hId|, |hbaredom|: no producer |
| |qU|, |mU|, |hmU|, |pc|, |hLB|, |hRB| | block pool |UpperPoolLowerBound qU mU pc datum|, reverse bound |UpperPoolReverseBound qU mU pc datum| | main.tex definition general-gluing-two-classes; lower bound = weak-duality identity, reverse bound = upper localization identity | |hLB|: producers |upperPoolLowerBound_of_blockwiseWeakDuality| / |upperPoolLowerBound_of_localReadout| (|FinslerOriginalUpperPoolDuality:270/297|) reduce it to blockwise weak duality plus block decompositions; |hRB|: only |upperPoolReverseBound_of_attainment| (:203) from the envelope, no closed producer |
| |dataIntr|, |hpcIntr| | |PopDataIntrinsic F u qU mU hmU ...| and pool consistency | paper frozen-bound/upper-localization chain | the intrinsic bound and guarded freezing produce the actual iid localization via |physicalWeightedLocalizationFamily_of_intrinsicPointwiseBound|; constructing |PopDataIntrinsic| from the population remains an input |

No unfinished proofs and no added axioms occur; every declaration stays within
the project's permitted axiom set (|propext|, |Classical.choice|, |Quot.sound|).
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability
  TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
  BigOperators

noncomputable section

namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}
  {A B : Set M}

/-- The stationary pressure datum family of the actual population, built from the
stationary forward datum of the weighted stationary matching class (the `C_w` /
`C_2` decomposition of the paper). -/
noncomputable def consolidatedStationaryDatum
    (α β : Measure UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (C : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ C φ)
    (hf : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    {G Cb : ℝ}
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor2 φ) ≤ Cb) :
    FinalProbeSpace A B → StationaryPressureDatum (StationaryForwardMatching α β) G Cb :=
  fun φ => stationaryForwardDatum (Ag φ) (fg φ) (G := G) (Cb := Cb) (C := C φ)
    (hA_meas φ) (hA_nonneg φ) (hA_bound φ) (hf φ) (hfG φ)
    (competitor φ) (hcompetitor φ) (hcompetitor_K φ)
    (competitor2 φ) (hcompetitor2 φ) (hcompetitor2_K φ)

/-- **The paper endgame data with all newly landed producers wired in.**

`hC` is derived from P1 (`PopulationFocalValueLimit`) + P2 (`FrozenAttainment`)
via `frozenCampbellReadout_of_populationFocalValueLimit_and_attainment`; `hU` is
derived from the lower-bound paper identity and the reverse bound via
`actualUpperReadout_of_lowerBound_and_reverseBound`; `hprob` is the unshifted
F12 paper producer consuming the paper's bare domination `hbaredom`
(`finalProbLowerData_of_frozen_domination`); `hscreen` is derived from the
uniform-elliptic identification of the stationary classes
(`weightedClass_eq_secondMomentClass_of_uniform_elliptic`); and the upper bundle
is built at the intrinsic F13 interface
(`physicalWeightedLocalizationFamily_of_intrinsicPointwiseBound` composed with
`endgameUpperFields_of_weightedLocalization`). -/
noncomputable def paperEndgameData_actual_consolidated
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (sample n))
    (hYi : ∀ n, iIndepFun (Y n) (sample n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)),
      (sample n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)),
      (sample n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (sample n))
    (Seed : ℕ → F.CalibratedSeedWindow
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB))
    (a : M → (ℚ → M))
    (κ : ∀ j, Measure (Seed j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) [IsFiniteMeasure lambda]
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB) ↦
      (a x.val, (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB) x.val)))
    (seedDatum : PaperGeometricSeedDatum F
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁))
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (ρl₀ ρl₁ : M → ℝ) (vf : ℕ → E → ℝ) (bf : (ℚ → M) × ℝ → M)
    (Good : (ℚ → M) → Prop) (r : ℝ) (δ loss : ℝ≥0∞)
    (Dl : PopulationLocalPressureCore Seed a κ lambda η₀ η₁ ρl₀ ρl₁ vf bf Good r δ loss)
    (εt : ℝ) (T : Dl.TaylorTiles εt)
    (α β : Measure UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (C : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ C φ)
    (hf_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    {G Cb : ℝ}
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor2 φ) ≤ Cb)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) → StationaryForwardMatching α β)
    (q : ℝ)
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M),
      FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z))
    (hAcoef : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hprobe : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        probeFam φ j z p.1 p.2))
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ)
      (z : ℚ → M) (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hP2 : FrozenAttainment (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q)
    (c : ℝ) (hc : 0 < c) (hA_low : ∀ (φ : FinalProbeSpace A B) (x y : ℝ),
      c ≤ (Ag φ) x y)
    (frozenCost : (f : FinalProbeSpace A B) → ℝ → ∀ n, Ω n → ℝ)
    (hId : RootedTileCampbellMeanIdentification Seed a κ lambda
      (frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        (Z := ℚ → M) α β coef probeFam Mst q) q sample frozenCost T.Index)
    (hbaredom : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      frozenCost f t n s ≤
        finslerSupportedPressure F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx => Or.inl hx) (hνB.mono fun _ hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s)
          (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
            hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hfrozen_int : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (sample n))
    (qU mU : ℕ) (hmU : 0 < mU)
    (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    (hLB : UpperPoolLowerBound qU mU pc
      (consolidatedStationaryDatum α β Ag fg C hA_meas hA_nonneg hA_bound
        hf_meas hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K))
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (dataIntr : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopDataIntrinsic F
        (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
          hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpcIntr : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin qU → Fin mU), (dataIntr f t hpert).p c t = pc f t c)
    (hRB : UpperPoolReverseBound qU mU pc
      (consolidatedStationaryDatum α β Ag fg C hA_meas hA_nonneg hA_bound
        hf_meas hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K)) :
    FinslerPaperEndgameData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB sample X Y
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB) := by
  classical
  let u := paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
    hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  have hu : (letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :=
    paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
      hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  let gread : FinalProbeSpace A B → ℝ → (ℚ → M) → ℝ :=
    frozenRootedCostReadout (F := F) (u := u) (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (Z := ℚ → M) α β coef probeFam Mst q
  let datum : FinalProbeSpace A B →
      StationaryPressureDatum (StationaryForwardMatching α β) G Cb :=
    consolidatedStationaryDatum α β Ag fg C hA_meas hA_nonneg hA_bound hf_meas
      hfG competitor competitor2 hcompetitor hcompetitor_K hcompetitor2
      hcompetitor2_K
  have hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) gread q datum :=
    frozenCampbellReadout_of_populationFocalValueLimit_and_attainment hF hcomplete
      hu ha hinj α β Ag fg C hA_meas hA_nonneg hA_bound hf_meas hfG competitor
      competitor2 hcompetitor hcompetitor_K hcompetitor2 hcompetitor2_K coef
      probeFam Mst q hM hAcoef hprobe hprobe_bound hP1 hP2
  have hU : UpperStationaryReadout
      (endgameUpperPressure_actual (A := A) (B := B) qU mU pc) datum :=
    actualUpperReadout_of_lowerBound_and_reverseBound qU mU pc datum hLB hRB
  have hscreen : StationaryScreening datum := by
    intro f v Q hQ ε hε
    refine ⟨Q, ?_, ?_⟩
    · show Q ∈ secondMomentClass α β
      have hcls := weightedClass_eq_secondMomentClass_of_uniform_elliptic
        (α := α) (β := β) (A := Ag f) (C := C f) (hA_meas f) hc (hA_low f)
        (hA_bound f)
      exact hcls ▸ hQ
    · linarith
  have hprob : FinalProbLowerData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB sample X Y u
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda gread q) (fun _ => 1) :=
    finalProbLowerData_of_frozen_domination (F := F) (u := u) (P := Seed) (a := a)
      (κ := κ) (lambda := lambda) (q := q) (D := Dl) (T := T) (ε := εt)
      hcomplete hdim ωM ρ₀ ρ₁ hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw
      hYlaw hXY u hu (fun _ => 1) gread frozenCost hId hbaredom hfrozen_int
  have hLoc := physicalWeightedLocalizationFamily_of_intrinsicPointwiseBound (F := F)
    (φ := u) hu hcomplete hdim ωM ρ₀ ρ₁ hA hB hAB hμA hνB sample X Y hX hY hXi
    hYi hXlaw hYlaw hXY qU mU hmU (fun _ => (1 : ℝ)) pc dataIntr hpcIntr
  have hLoc' : PhysicalWeightedLocalizationFamily F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB sample X Y u
      (fun _ : Fin qU → Fin mU => 1 / (((mU ^ qU : ℕ) : ℝ))) pc (fun _ => 1) := by
    simpa [show (fun c : Fin qU → Fin mU =>
        ((blockW qU mU hmU c : unitInterval) : ℝ)) =
        (fun _ => 1 / (((mU ^ qU : ℕ) : ℝ))) from by funext c; rfl] using hLoc
  let U := endgameUpperFields_of_weightedLocalization qU mU (fun _ => 1) hLoc'
    (endgameUpperPressure_actual qU mU pc) (fun f t _ => rfl)
  have hUr : U.radius = fun _ => 1 := rfl
  exact paperEndgameData_of_upperBundle hF hu seedDatum hprob U hUr
    (W := StationaryForwardMatching α β) (G := G) (Cb := Cb) (datum := datum)
    hC hU hscreen



/-- **The paper selector theorem at the derived calibrated potential, consuming the
consolidated endgame data.**  The potential is the named `paperCalibratedPotential`
(no `u`/`hu` binder), the endgame data are produced by
`paperEndgameData_actual_consolidated` (F15 from P1+P2, F18 from the lower + reverse
bounds, F12 from the paper's bare domination, screening from the uniform-elliptic
class identification, F13 at the intrinsic interface). The readout tilt derivative
is derived from those endgame data at the calibrated potential. -/
theorem existsUnique_general_finsler_selector_at_derivedPotential_consolidated
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (sample n))
    (hYi : ∀ n, iIndepFun (Y n) (sample n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)),
      (sample n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)),
      (sample n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (sample n))
    (Seed : ℕ → F.CalibratedSeedWindow
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB))
    (a : M → (ℚ → M))
    (κ : ∀ j, Measure (Seed j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) [IsFiniteMeasure lambda]
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB) ↦
      (a x.val, (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB) x.val)))
    (seedDatum : PaperGeometricSeedDatum F
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁))
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (ρl₀ ρl₁ : M → ℝ) (vf : ℕ → E → ℝ) (bf : (ℚ → M) × ℝ → M)
    (Good : (ℚ → M) → Prop) (r : ℝ) (δ loss : ℝ≥0∞)
    (Dl : PopulationLocalPressureCore Seed a κ lambda η₀ η₁ ρl₀ ρl₁ vf bf Good r δ loss)
    (εt : ℝ) (T : Dl.TaylorTiles εt)
    (α β : Measure UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (C : FinalProbeSpace A B → ℝ)
    (hA_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (Ag φ) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), 0 ≤ (Ag φ) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (x y : ℝ), (Ag φ) x y ≤ C φ)
    (hf_meas : ∀ φ : FinalProbeSpace A B,
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => (fg φ) p.1 p.2))
    {G Cb : ℝ}
    (hfG : ∀ (φ : FinalProbeSpace A B) (x y : MarkedCloudPoint), |(fg φ) x y| ≤ G)
    (competitor competitor2 : FinalProbeSpace A B → StationaryForwardMatching α β)
    (hcompetitor : ∀ φ : FinalProbeSpace A B,
      FiniteWeightedKinetic (Ag φ) (competitor φ))
    (hcompetitor_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor φ) ≤ Cb)
    (hcompetitor2 : ∀ φ : FinalProbeSpace A B, (competitor2 φ).FiniteSecondMoment)
    (hcompetitor2_K : ∀ φ : FinalProbeSpace A B,
      palmKinetic (Ag φ) (competitor2 φ) ≤ Cb)
    (coef : FinalProbeSpace A B → ℕ → (ℚ → M) → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → (ℚ → M) →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mst : FinalProbeSpace A B → ℝ → ℕ → (ℚ → M) → StationaryForwardMatching α β)
    (q : ℝ)
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M),
      FiniteWeightedKinetic (coef φ j z) ((Mst φ t) j z))
    (hAcoef : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hprobe : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : ℚ → M),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        probeFam φ j z p.1 p.2))
    (hprobe_bound : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ)
      (z : ℚ → M) (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hP2 : FrozenAttainment (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) α β coef probeFam Mst q)
    (c : ℝ) (hc : 0 < c) (hA_low : ∀ (φ : FinalProbeSpace A B) (x y : ℝ),
      c ≤ (Ag φ) x y)
    (frozenCost : (f : FinalProbeSpace A B) → ℝ → ∀ n, Ω n → ℝ)
    (hId : RootedTileCampbellMeanIdentification Seed a κ lambda
      (frozenRootedCostReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        (Z := ℚ → M) α β coef probeFam Mst q) q sample frozenCost T.Index)
    (hbaredom : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      frozenCost f t n s ≤
        finslerSupportedPressure F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx => Or.inl hx) (hνB.mono fun _ hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s)
          (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
            hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hfrozen_int : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (sample n))
    (qU mU : ℕ) (hmU : 0 < mU)
    (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    (hLB : UpperPoolLowerBound qU mU pc
      (consolidatedStationaryDatum α β Ag fg C hA_meas hA_nonneg hA_bound
        hf_meas hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K))
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (dataIntr : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopDataIntrinsic F
        (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
          hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpcIntr : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin qU → Fin mU), (dataIntr f t hpert).p c t = pc f t c)
    (hRB : UpperPoolReverseBound qU mU pc
      (consolidatedStationaryDatum α β Ag fg C hA_meas hA_nonneg hA_bound
        hf_meas hfG competitor competitor2 hcompetitor hcompetitor_K
        hcompetitor2 hcompetitor2_K)) :
    let u := paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
    let hu : (letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :=
      paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
    let D := paperEndgameData_actual_consolidated hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY Seed a κ lambda ha hinj seedDatum η₀ η₁ ρl₀ ρl₁ vf bf Good r δ loss Dl εt T α β Ag fg C hA_meas hA_nonneg hA_bound hf_meas hfG competitor competitor2 hcompetitor hcompetitor_K hcompetitor2 hcompetitor2_K coef probeFam Mst q hM hAcoef hprobe hprobe_bound hP1 hP2 c hc hA_low frozenCost hId hbaredom hfrozen_int qU mU hmU pc hLB dataIntr hpcIntr hRB
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    Nonempty (FinslerSelectorFinalInputs F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) hA hB hμA hνB sample X Y u) ∧
        Tendsto (fun n => D.geometric.palm_sample_law.normalization n *
          D.geometric.palm_sample_law.maskedMean n -
          D.geometric.palm_sample_law.populationValue n) atTop (𝓝 0) ∧
        ∃ derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ,
          (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
            HasDerivAt (fun t => D.pressureLower f t) (derivative f) 0) ∧
          ∃! π : ProbabilityMeasure (M × M),
            (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
              ∫ z, f z ∂((π : Measure (M × M)).comap
                (Prod.map ((↑) : ↥(A ∪ B) → M) ((↑) : ↥(A ∪ B) → M))) = derivative f) ∧
            (∀ U ∈ 𝓝 π, Tendsto (fun n => (sample n).real
              {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                (fun i => X n i s) (fun i => Y n i s), γ ∉ U}) atTop (𝓝 0)) ∧
            (∀ d : ProbabilityMeasure (M × M) → ProbabilityMeasure (M × M) → ℝ,
              d π π = 0 →
              (∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (M × M) | d γ π < ε}) →
              ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sample n).real
                {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                  (fun i => X n i s) (fun i => Y n i s), ε ≤ d γ π}) atTop (𝓝 0)) ∧
            IsOptimalCoupling edist
              (physicalSourceProbability ωM ρ₀ : Measure M)
              (physicalTargetProbability ωM ρ₁ : Measure M) (π : Measure (M × M))
        := by
  classical
  let u := paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  let hu : (letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :=
    paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  let D := paperEndgameData_actual_consolidated hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY Seed a κ lambda ha hinj seedDatum η₀ η₁ ρl₀ ρl₁ vf bf Good r δ loss Dl εt T α β Ag fg C hA_meas hA_nonneg hA_bound hf_meas hfG competitor competitor2 hcompetitor hcompetitor_K hcompetitor2 hcompetitor2_K coef probeFam Mst q hM hAcoef hprobe hprobe_bound hP1 hP2 c hc hA_low frozenCost hId hbaredom hfrozen_int qU mU hmU pc hLB dataIntr hpcIntr hRB
  have hd : FinslerReadoutTiltDerivative D.pressureLower :=
    finslerReadoutTiltDerivative_of_paperEndgameData hF hcomplete hdim m ωM ρ₀ ρ₁
      hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
      sample X Y hX hY hXi hYi hXlaw hYlaw hXY D
  exact existsUnique_general_finsler_selector_at_potential_paperData hF hcomplete
    hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB
    hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY u hu D hd

end OTSelector.Reconstruction

end
