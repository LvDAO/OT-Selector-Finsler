import OTSelector.Reconstruction.FinslerOriginalRootedDataMeasurability
import OTSelector.Reconstruction.FinslerOriginalCampbellMeanBound

/-!
# Wiring the assembled scene collapse into the pressure chain

FinslerOriginalRootedDataMeasurability.lean proves the final assembled scene
collapse: from one paper-level frozen-data measurability statement and the frozen
data hypotheses, the frozen Campbell cost equals the limiting Palm readout
constant Psi.  This module wires that collapse into the pressure chain of
FinslerGeneralSelectorAssemblyFinal.lean.

## The lower pressure readout

The lower-pressure input of the final assembly is a function
pressureLower : ((K x K) ->b R) -> R -> R whose intended value at (f, t) is the
population limit of the empirical frozen pressure.  The assembled collapse shows
that the frozen Campbell cost is exactly that population limit, so we name it:

* frozenPressureLower Seed a kappa lambda g q := fun f t =>
  campbellAveragedFrozenCost Seed a kappa lambda (g f t) q;

* frozenPressureLower_eq_sceneReadout_of_frozenData: from the paper data
  hypotheses (hData, G, hMK, hcover, hunithaar, hconst) the frozen lower pressure
  equals the assembled Palm readout Psi;

* pressureLower_eq_sceneReadout_of_empirical_limit: any pressureLower whose
  empirical means converge to it and whose population mean bounds bracket the
  frozen Campbell cost (lower bound from the named tile-level Campbell mean
  identification RootedTileCampbellMeanIdentification, upper bound as the
  corresponding upper mean bound) equals the assembled Palm readout Psi.

## Exact remaining data wiring

The only remaining inputs of the pressure chain are:

* the tile-level Campbell mean identification
  RootedTileCampbellMeanIdentification (lower population mean bound), which is
  the limit-law content supplied by the probability lane;
* the corresponding upper population mean bound for the empirical frozen
  pressure (to pin the limit from above);
* the identification of the assembly pressureLower function with the
  population limit of the empirical frozen pressure, and separately the upper
  pressure chain giving hvalue.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  [Fintype ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {K : Set M}

/-- **The frozen lower-pressure readout.**

The function on probes and tilts whose value at (f, t) is the frozen Campbell
cost of the frozen readout family g f t.  This is the assembled population limit
of the empirical frozen pressure. -/
noncomputable def frozenPressureLower
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) (q : ℝ) :
    ((K × K) →ᵇ ℝ) → ℝ → ℝ :=
  fun f t ↦ campbellAveragedFrozenCost Seed a κ lambda (g f t) q

/-- **The frozen lower pressure equals the assembled Palm readout.**

From the paper data hypotheses — one joint measurability statement for the frozen
data, the uniform probe bound, the finite weighted kinetic class of the rooted
scene carrier, a.e. coverage and unit density of the root partition, the frozen
gluing of the readout family, and the Palm readout constancy — the frozen lower
pressure readout is exactly the assembled limiting Palm readout Psi. -/
theorem frozenPressureLower_eq_sceneReadout_of_frozenData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    [IsProbabilityMeasure lambda]
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ)
    {q : ℝ} (hq : 2 < q)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPressureWiringMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, SigmaFinite (κ j)]
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hData : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      Measurable (fun q' : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        ((Acoef f t) j q'.1 q'.2.1.1 q'.2.2.1,
          (fprobe f t) j q'.1 q'.2.1 q'.2.2)))
    {G : ℝ} (hG : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |(fprobe f t) j z x y| ≤ G)
    (hMK : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ) (z : Z),
      StationaryForwardMatching.FiniteWeightedKinetic ((Acoef f t) j z)
        (rootedSceneRootCarrier Q hforward))
    (hglue : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece Seed a κ lambda j),
        g f t z = atlasRootFrozenIntegrand
          ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
          ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
          Seed a κ lambda Acoef fprobe
          (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q t f j z)
    (hcover : ∀ᵐ z ∂lambda,
      z ∈ ⋃ j, populationSeedRootPiece Seed a κ lambda j)
    (hunithaar : ∀ j, ∀ᵐ z ∂lambda.restrict
      (populationSeedRootPiece Seed a κ lambda j),
      populationAtlasTheta Seed a κ lambda j z = 1)
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hconst : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (j : ℕ),
      ∀ᵐ w ∂((κ j).restrict
        (populationSeedRootLabelValue (Seed j).seed a ''
          populationSeedRootPiece Seed a κ lambda j)),
        rootedScenePalmReadout Q
          (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
            ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
            (t * populationAtlasTheta Seed a κ lambda j
              (a ((Seed j).seed.curve w 0)) ^ (2 / q))) = Ψ f t) :
    frozenPressureLower Seed a κ lambda g q = Ψ := by
  funext f t
  exact campbellAveragedFrozenCost_eq_palmReadout_of_sceneLimit_data
    Seed a κ lambda Acoef fprobe hq hF hcomplete hu ha hinj Q hforward
    hData hG hMK f t (g f t) (hglue f t) hcover hunithaar (Ψ f t) (hconst f t)

/-- **The pressureLower input of the final assembly is the assembled readout.**

Suppose the assembly pressureLower function is the population limit of the
empirical frozen pressure: the empirical means converge to it, the lower
population mean is bounded below by the frozen Campbell cost (the named
tile-level Campbell mean identification), and the corresponding upper population
mean bound holds.  Then the assembly pressureLower is exactly the assembled
limiting Palm readout Psi. -/
theorem pressureLower_eq_sceneReadout_of_empirical_limit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hId : OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.RootedTileCampbellMeanIdentification
      Seed a κ lambda g q P frozenCost ιt)
    (hlim : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, frozenCost f t n s ∂P n) atTop
        (𝓝 (pressureLower f t)))
    (hUp : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, frozenCost f t n s ∂P n ≤
        frozenPressureLower Seed a κ lambda g q f t + ε)
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower Seed a κ lambda g q = Ψ) :
    pressureLower = Ψ := by
  funext f t
  have hmean :=
    OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.camFrozenMeanBound_of_rootedTileIdentification
      Seed a κ lambda g (P := P) (frozenCost := frozenCost) (q := q) hId
  have hle : frozenPressureLower Seed a κ lambda g q f t ≤ pressureLower f t := by
    by_contra hcon
    have hcon' : pressureLower f t < frozenPressureLower Seed a κ lambda g q f t :=
      not_le.mp hcon
    have hε : 0 < (frozenPressureLower Seed a κ lambda g q f t -
        pressureLower f t) / 2 := by linarith
    have hev := hmean f t ((frozenPressureLower Seed a κ lambda g q f t -
      pressureLower f t) / 2) hε
    have hconst : Tendsto (fun _ : ℕ ↦
        frozenPressureLower Seed a κ lambda g q f t -
          (frozenPressureLower Seed a κ lambda g q f t -
            pressureLower f t) / 2) atTop
        (𝓝 (frozenPressureLower Seed a κ lambda g q f t -
          (frozenPressureLower Seed a κ lambda g q f t -
            pressureLower f t) / 2)) := tendsto_const_nhds
    have hlim' := le_of_tendsto_of_tendsto hconst (hlim f t) (by
      filter_upwards [hev] with n hn
      exact hn)
    linarith
  have hge : pressureLower f t ≤ frozenPressureLower Seed a κ lambda g q f t := by
    by_contra hcon
    have hcon' : frozenPressureLower Seed a κ lambda g q f t < pressureLower f t :=
      not_le.mp hcon
    have hε : 0 < (pressureLower f t -
        frozenPressureLower Seed a κ lambda g q f t) / 2 := by linarith
    have hev := hUp f t ((pressureLower f t -
      frozenPressureLower Seed a κ lambda g q f t) / 2) hε
    have hconst : Tendsto (fun _ : ℕ ↦
        frozenPressureLower Seed a κ lambda g q f t +
          (pressureLower f t -
            frozenPressureLower Seed a κ lambda g q f t) / 2) atTop
        (𝓝 (frozenPressureLower Seed a κ lambda g q f t +
          (pressureLower f t -
            frozenPressureLower Seed a κ lambda g q f t) / 2)) :=
      tendsto_const_nhds
    have hlim' := le_of_tendsto_of_tendsto (hlim f t) hconst (by
      filter_upwards [hev] with n hn
      exact hn)
    linarith
  have hfroz : pressureLower f t = frozenPressureLower Seed a κ lambda g q f t :=
    le_antisymm hge hle
  rw [hfroz]
  exact congrFun (congrFun hread f) t

end OTSelector.Reconstruction