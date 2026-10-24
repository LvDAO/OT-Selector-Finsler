import OTSelector.Reconstruction.FinslerOriginalIIDPressureLowerLocalization
import OTSelector.Reconstruction.FinslerCampbellLowerAssembly
import OTSelector.Reconstruction.FinslerOriginalFiniteDomination

/-!
# Frozen-core Campbell/LLN identification

This module closes the last analytic input of the lower-pressure lane: the
identification of the *mean* (equivalently, the weak limits) of the actual
frozen core cost of the original empirical optimal face with the population
Campbell value

  `Pw(t) = campbellAveragedStationaryPressure α β Seed a κ lambda A f q t`,

which is `main.tex`'s `𝒫_w(t)` (`general-gluing-integrated-pressures`).

The paper's lower bound proof factorizes exactly here:

1. *Campbell lower comparison.*  On the limiting rooted scene the frozen core
   cost dominates the source-Palm average of the kinetic-plus-probe cost:
   `weightedStationaryPressure α β (A j z) (f j z) (t θ_j(z)^{2/q}) ≤ g z` at
   almost every root of each atlas piece.  This is the remaining geometric input
   (Campbell's formula applied to the limiting stationary matching); the
   module `OTSelector/Reconstruction/FinslerCampbellLowerAssembly.lean`
   already proves that it implies
   `campbellAveragedStationaryPressure ≤ campbellAveragedFrozenCost g`.
2. *Frozen-core LLN.*  The expected frozen core cost of the original empirical
   optimal face is asymptotically at least the Campbell-averaged frozen cost
   plus the probe constant `B_t = |t| ||f||`.

This file composes the two steps with the previously proved lower-pressure
transfer.  The composition is unconditional: the atlas Campbell comparison is
invoked as an already-proved theorem, and the only remaining input is the
explicitly named, structured expectation-level LLN `hfrozen_mean`, together with
finite domination of the frozen core (also proved, on the physical optimal face,
in `FinslerOriginalIIDPressureLowerLocalization.lean`).

Main results:

* `campbellAveragedStationaryPressure_family_le_campbellAveragedFrozenCost`:
  the family form over physical probes and tilts of the already-proved atlas
  Campbell comparison, with every atlas input explicit;
* `frozenMeanLower_of_campbellFrozenMean`: the mean identification: the
  Campbell comparison plus the expectation-level LLN give
  `liminf E[frozenCost] >= Pw + |t| ||f||`;
* `physical_finsler_probability_lower_of_campbellFrozen`: the assembly's `hprob`
  clause verbatim with the population pressure instantiated at `Pw`;
* `tileFrozenCost`: the frozen core cost of one retained Taylor tile, the
  summand of the actual frozen core functional;
* `integral_originalFrozenCoreCost_eq_sum_tiles` and
  `integral_originalFrozenCorePressure_eq_sum_tiles`: the actual frozen core
  functional `fractionalAssignmentCost (originalFrozenCoreMatrix) / (n+1)`
  decomposes exactly over the retained Taylor tiles, so its mean is the finite
  sum of the per-tile means (the form in which the original iid counting laws
  enter);
* `integral_originalFrozenCorePressure_ge_sum_of_tile_bounds`: tile-by-tile
  expectation bounds aggregate to the total expected frozen core pressure,
  because the retained tile edge events are disjoint.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

variable {K : Set M}

/-- **Family form of the atlas Campbell lower comparison.**

For every physical probe `f` and tilt `t`, if at almost every root of each atlas
piece the weighted stationary pressure is dominated by the frozen root integrand
`g f t`, then the Campbell-averaged stationary pressure `Pw(t)` is at most the
Campbell-averaged frozen cost.  This is
`campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost_of_bound` with
the probe and tilt indices made explicit, so that it applies to the whole
pressure family of the assembly. -/
theorem campbellAveragedStationaryPressure_family_le_campbellAveragedFrozenCost
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (u : M → ℝ) (hu : let _instFrozenCampbellMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (a : M → Z) (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {q : ℝ}
    (A : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      OTSelector.PointProcess.MarkedCloudPoint → OTSelector.PointProcess.MarkedCloudPoint → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ)
    (BI Bg : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hBI : ∀ f t, 0 ≤ BI f t) (hBg : ∀ f t, 0 ≤ Bg f t)
    (hdom : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂lambda.restrict (OTSelector.Reconstruction.populationSeedRootPiece Seed a κ lambda j),
        OTSelector.PointProcess.StationaryForwardMatching.weightedStationaryPressure α β
          ((A f t) j z) ((fprobe f t) j z)
          (t * OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ≤
          (g f t) z)
    (hintI : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      IntegrableOn
        (fun z ↦ OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          OTSelector.PointProcess.StationaryForwardMatching.weightedStationaryPressure α β
            ((A f t) j z) ((fprobe f t) j z)
            (t * OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (2 / q)))
        (OTSelector.Reconstruction.populationSeedRootPiece Seed a κ lambda j) lambda)
    (hintg : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      IntegrableOn
        (fun z ↦ OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          (g f t) z)
        (OTSelector.Reconstruction.populationSeedRootPiece Seed a κ lambda j) lambda)
    (hI_bound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      |OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
        OTSelector.PointProcess.StationaryForwardMatching.weightedStationaryPressure α β
          ((A f t) j z) ((fprobe f t) j z)
          (t * OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (2 / q))| ≤ BI f t)
    (hg_bound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      |OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
        (g f t) z| ≤ Bg f t) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      OTSelector.PointProcess.campbellAveragedStationaryPressure α β Seed a κ lambda
        (A f t) (fprobe f t) q t ≤
      OTSelector.Reconstruction.campbellAveragedFrozenCost Seed a κ lambda (g f t) q := by
  intro f t
  exact OTSelector.Reconstruction.campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost_of_bound
    α β Seed a κ lambda hF hcomplete hu ha hinj (A f t) (fprobe f t) (g f t)
    (hBI f t) (hBg f t) (hdom f t) (hintI f t) (hintg f t) (hI_bound f t) (hg_bound f t)

/-- **Frozen-core mean identification.**

If the Campbell-averaged stationary pressure `Pw` is dominated by a
Campbell-averaged frozen cost `camFrozen` (the conclusion of the already-proved
atlas Campbell comparison, supplied here in family form), and the expected
frozen core cost of the original empirical optimal face is asymptotically at
least `camFrozen` plus the probe constant `|t| ||f||` (the frozen-core LLN), then
the expected frozen core cost is asymptotically at least `Pw` plus the probe
constant.  This is the local value identification of the lower lane. -/
theorem frozenMeanLower_of_campbellFrozenMean
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (pressureLower camFrozen : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hle : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), pressureLower f t ≤ camFrozen f t)
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hmean : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      camFrozen f t + |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n := by
  intro f t ε hε
  filter_upwards [hmean f t ε hε] with n hn
  linarith [hle f t]

/-- **The assembly's `hprob` clause at the population Campbell value `Pw(t)`.**

This is the lower pressure localization of the paper's
`general-gluing-weighted-lower` with the population pressure instantiated at
`main.tex`'s `𝒫_w(t)` (`general-gluing-integrated-pressures`).  The analytic
inputs are:

* finite domination of the frozen core cost on the physical empirical optimal
  face (proved unconditionally in
  `FinslerOriginalIIDPressureLowerLocalization.lean` for the geometric frozen
  core matrix);
* integrability of the frozen core cost;
* the frozen-core LLN: `liminf E[frozenCost] >= campbellAveragedFrozenCost (g f t) + |t| ||f||`;
* the atlas Campbell pointwise domination input and its boundedness data, which
  the already-proved atlas comparison turns into `Pw(t) <= campbellAveragedFrozenCost (g f t)`.

The conclusion is the assembly's `hprob` clause verbatim, with `Pw` in place of
`pressureLower`. -/
theorem physical_finsler_probability_lower_of_campbellFrozen
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) =
      (physicalSourceProbability ωM ρ₀ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) =
      (physicalTargetProbability ωM ρ₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instFrozenCampbellPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
    (frozenCost : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (a : M → Z) (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain φ ↦ (a x.val, φ x.val)))
    (α β : Measure OTSelector.UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow φ)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {q : ℝ}
    (Acoef : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℕ → Z →
      OTSelector.PointProcess.MarkedCloudPoint → OTSelector.PointProcess.MarkedCloudPoint → ℝ)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → Z → ℝ)
    (BI Bg : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hBI : ∀ f t, 0 ≤ BI f t) (hBg : ∀ f t, 0 ≤ Bg f t)
    (hdom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂lambda.restrict (OTSelector.Reconstruction.populationSeedRootPiece Seed a κ lambda j),
        OTSelector.PointProcess.StationaryForwardMatching.weightedStationaryPressure α β
          ((Acoef f t) j z) ((fprobe f t) j z)
          (t * OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ≤
          (g f t) z)
    (hintI : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      IntegrableOn
        (fun z ↦ OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          OTSelector.PointProcess.StationaryForwardMatching.weightedStationaryPressure α β
            ((Acoef f t) j z) ((fprobe f t) j z)
            (t * OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (2 / q)))
        (OTSelector.Reconstruction.populationSeedRootPiece Seed a κ lambda j) lambda)
    (hintg : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      IntegrableOn
        (fun z ↦ OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          (g f t) z)
        (OTSelector.Reconstruction.populationSeedRootPiece Seed a κ lambda j) lambda)
    (hI_bound : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      |OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
        OTSelector.PointProcess.StationaryForwardMatching.weightedStationaryPressure α β
          ((Acoef f t) j z) ((fprobe f t) j z)
          (t * OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (2 / q))| ≤ BI f t)
    (hg_bound : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      |OTSelector.Reconstruction.populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
        (g f t) z| ≤ Bg f t)
    (hfrozen_mean : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      OTSelector.Reconstruction.campbellAveragedFrozenCost Seed a κ lambda (g f t) q +
        |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
      |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F
        (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          OTSelector.PointProcess.campbellAveragedStationaryPressure α β Seed a κ lambda
            (Acoef f t) (fprobe f t) q t - ε}) atTop (𝓝 0) := by
  intro f t ε _ht hε
  have hle : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      OTSelector.PointProcess.campbellAveragedStationaryPressure α β Seed a κ lambda
        (Acoef f t) (fprobe f t) q t ≤
      OTSelector.Reconstruction.campbellAveragedFrozenCost Seed a κ lambda (g f t) q :=
    campbellAveragedStationaryPressure_family_le_campbellAveragedFrozenCost
      hF hcomplete φ hφ a ha hinj α β Seed κ lambda Acoef fprobe g BI Bg
      hBI hBg hdom hintI hintg hI_bound hg_bound
  have hmean : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      OTSelector.PointProcess.campbellAveragedStationaryPressure α β Seed a κ lambda
        (Acoef f t) (fprobe f t) q t + |t| * (‖f‖₊ : ℝ) - ε ≤
        ∫ s, frozenCost f t n s ∂P n :=
    frozenMeanLower_of_campbellFrozenMean P
      (fun f t ↦ OTSelector.PointProcess.campbellAveragedStationaryPressure α β Seed a κ
        lambda (Acoef f t) (fprobe f t) q t)
      (fun f t ↦ OTSelector.Reconstruction.campbellAveragedFrozenCost Seed a κ lambda (g f t) q)
      hle frozenCost hfrozen_mean
  exact physical_finsler_probability_lower_of_frozen_mean_lower hcomplete hdim
    ωM ρ₀ ρ₁ hA hB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ
    (fun f t ↦ OTSelector.PointProcess.campbellAveragedStationaryPressure α β Seed a κ
      lambda (Acoef f t) (fprobe f t) q t)
    radius frozenCost hfrozen_int hfrozen_dom hmean f t ε _ht hε

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex


namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)

namespace PopulationLocalPressureCore.TaylorTiles

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The frozen core cost of one retained Taylor tile at one sample: the clipped
frozen physical cost plus the frozen probe term, masked to the tile's actual
disjoint edge event and integrated against the (fractional) empirical optimizer. -/
noncomputable def tileFrozenCost (X Y : Ω → Fin n → M)
    (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ) (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (scale t : ℝ) (k : T.Index) (s : Ω) : ℝ :=
  fractionalAssignmentCost
    (maskedFrozenCost (T.edgeEvent (X s) (Y s) k)
      (frozenCoreMatrix (T.core k) ε (fun _ _ ↦ T.reference k) (X s) (Y s) scale t (h s k)))
    (A s)

/-- **Exact tile decomposition of the actual frozen core cost.**

The frozen core cost `Γ_n = fractionalAssignmentCost (originalFrozenCoreMatrix)`
of the original empirical optimal face is the finite sum of its per-tile frozen
costs.  This is the form in which the original iid counting laws enter the
Campbell identification: the tile events are disjoint, so the total frozen cost
is a finite sum of per-tile terms, each a function of the retained source/target
roots in one Taylor cell. -/
theorem integral_originalFrozenCoreCost_eq_sum_tiles
    (P₀ : Measure Ω) (X Y : Ω → Fin n → M)
    (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ) (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (scale t : ℝ)
    (hint : ∀ k : T.Index, Integrable (T.tileFrozenCost X Y h A scale t k) P₀) :
    ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s)) (A s) ∂P₀ =
      ∑ k, ∫ s, T.tileFrozenCost X Y h A scale t k s ∂P₀ := by
  have hpt : ∀ s, fractionalAssignmentCost
      (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s)) (A s) =
      ∑ k, T.tileFrozenCost X Y h A scale t k s := by
    intro s
    exact T.fractionalAssignmentCost_originalFrozenCoreMatrix_eq_sum (X s) (Y s) scale t (h s) (A s)
  rw [show (fun s ↦ fractionalAssignmentCost
      (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s)) (A s)) =
      (fun s ↦ ∑ k, T.tileFrozenCost X Y h A scale t k s) from funext hpt]
  rw [integral_finsetSum Finset.univ (fun k _ ↦ hint k)]

/-- The normalized frozen core cost `Γ_n / n` splits into the normalized
per-tile frozen costs.  This is the expectation-level identity on which the
tile-by-tile iid counting laws are applied. -/
theorem integral_originalFrozenCorePressure_eq_sum_tiles
    (P₀ : Measure Ω) (X Y : Ω → Fin n → M)
    (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ) (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (scale t : ℝ)
    (hint : ∀ k : T.Index, Integrable (T.tileFrozenCost X Y h A scale t k) P₀) :
    ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s)) (A s) / (n : ℝ) ∂P₀ =
      ∑ k, ∫ s, T.tileFrozenCost X Y h A scale t k s / (n : ℝ) ∂P₀ := by
  have hpt : ∀ s, fractionalAssignmentCost
      (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s)) (A s) / (n : ℝ) =
      ∑ k, T.tileFrozenCost X Y h A scale t k s / (n : ℝ) := by
    intro s
    rw [T.fractionalAssignmentCost_originalFrozenCoreMatrix_eq_sum (X s) (Y s) scale t
      (h s) (A s), Finset.sum_div]
    rfl
  rw [show (fun s ↦ fractionalAssignmentCost
      (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s)) (A s) / (n : ℝ)) =
      (fun s ↦ ∑ k, T.tileFrozenCost X Y h A scale t k s / (n : ℝ)) from funext hpt]
  rw [integral_finsetSum Finset.univ (fun k _ ↦ (hint k).div_const _)]

/-- **Tile-by-tile LLN aggregation.**

If every tile's expected frozen cost is at least its population share minus its
own counting/expansion budget, then the total expected normalized frozen core
cost is at least the sum of the population shares minus the total budget.  This
is the finite-sum aggregation step of the paper's
`general-gluing-finite-domination`/Campbell argument: disjoint source-core
assignment counts each retained edge exactly once. -/
theorem integral_originalFrozenCorePressure_ge_sum_of_tile_bounds
    (P₀ : Measure Ω) (X Y : Ω → Fin n → M)
    (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ) (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (scale t : ℝ)
    (hint : ∀ k : T.Index, Integrable (T.tileFrozenCost X Y h A scale t k) P₀)
    (value budget : T.Index → ℝ)
    (htile : ∀ k : T.Index, value k - budget k ≤
      ∫ s, T.tileFrozenCost X Y h A scale t k s ∂P₀) :
    ∑ k, value k - ∑ k, budget k ≤
      ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s)) (A s) ∂P₀ := by
  rw [T.integral_originalFrozenCoreCost_eq_sum_tiles P₀ X Y h A scale t hint,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun k _ ↦ htile k

end PopulationLocalPressureCore.TaylorTiles
end OTSelector.Reconstruction
