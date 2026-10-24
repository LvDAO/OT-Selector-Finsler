import OTSelector.Probability.CavityProbeReadoutPortmanteau

/-!
# Final assembly of the rooted-scene probe readout

This module continues `CavityProbeReadoutPortmanteau` with the change-of-variables
half of the bridge between the scene-law integral and the root-averaged random
scene test.

`integral_cavitySceneTestFunctional_sceneLaw_eq` proves
`∫ s, cavitySceneTestFunctional base φ s ∂Q_n =
  ∫ v, cavitySceneTestFunctional base φ (scene v) ∂(P n × ρ)`,
where `Q_n` is the countable rooted scene law and `scene` is the actual scene map.

## Remaining gap

The second half of the bridge,
`cavitySceneTestFunctional base φ (scene (ω, z)) =
  ∫ e, φ e ∂(rooted plus plan) - ∫ e, φ e ∂(rooted minus plan)`
almost surely, followed by `integral_prod` and `integral_sub`, is not formalized
here.  It requires:
* unfolding `cavityRootedCountableScene`, `cavityRootedLocalScene` and
  `LocalFiniteMeasure.testIntegral`, and replacing `finitePlanLocalVersion` by
  the rooted plan on the feasible event using `coe_finitePlanLocalVersion` and
  `IsSemidiscreteAllocation.isFiniteMeasure_cavitySpatialRootedPlan`;
* the a.e. bound `|∫ φ e ∂(rooted plan)| ≤ N * Cη * Cg`, which follows from
  `integral_cavityMarkWindowTest_cavitySpatialRootedPlan` and the allocation
  cost bound (sum one and nonnegativity), to obtain integrability for Fubini.

Once that identity is available,
`tendsto_integral_cavitySceneTestFunctional_of_weak` yields the `hscene` input of
`tendsto_expectedProbeDifference_of_sceneTest`.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped BigOperators ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

section Final

variable [TopologicalSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [MetricSpace B] [CompactSpace B] [BorelSpace B] [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

open PointProcess PointProcess.LocalConfiguration

local instance finalBorelTarget : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance finalConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance finalConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance finalConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance finalPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance finalCloudPolish :
    PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- **Change of variables along the scene map.**  The scene-law integral of the
continuous scene functional is the environment-root integral of the composed
functional. -/
theorem integral_cavitySceneTestFunctional_sceneLaw_eq {Ω : Type*} [MeasurableSpace Ω]
    {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ))
    (hD : volume D = ENNReal.ofReal N)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ)) :
    ∫ s, cavitySceneTestFunctional base φ s
        ∂(cavityCountableSceneLawRootMeasure base P μ p hp aplus aminus
          hplusm hminusm Y hY N hN D hD :
          Measure (CavityCountableTargetScene (A := A) base))
      = ∫ v, cavitySceneTestFunctional base φ
          (cavityRootedCountableScene base μ p aplus aminus Y N v)
        ∂(P.prod (cavityRootMeasure volume D N)) := by
  haveI hρ : IsProbabilityMeasure (cavityRootMeasure volume D N) :=
    isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  have hmeas : Measurable
      (cavityRootedCountableScene base μ p aplus aminus Y N) :=
    measurable_cavityRootedCountableScene base μ p hp aplus aminus
      hplusm hminusm Y hY N
  have hcont : Continuous (cavitySceneTestFunctional base φ) :=
    continuous_cavitySceneTestFunctional base φ
  change ∫ s, cavitySceneTestFunctional base φ s
      ∂(Measure.map (cavityRootedCountableScene base μ p aplus aminus Y N)
        (P.prod (cavityRootMeasure volume D N))) = _
  rw [integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]

end Final

end OTSelector.Probability
