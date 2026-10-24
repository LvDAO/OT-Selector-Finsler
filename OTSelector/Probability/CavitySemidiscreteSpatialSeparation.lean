import OTSelector.Probability.CavitySemidiscreteCountableScene
import OTSelector.Probability.OriginalTargetConfigurationSeparation

/-!
# Actual common target scenes have spatially distinct occupied sites

The original iid array and its original normalized spatial marginal supply all
pair bounds. Their common weak limit therefore has an injective spatial target
projection; neither a Poisson law nor an additional geometric condition is used.
-/

open Function Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability
open PointProcess PointProcess.LocalConfiguration

variable {ι A B : Type*} [Fintype ι] [Nonempty ι]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [MetricSpace B] [ProperSpace B] [MeasurableSpace B]
  [BorelSpace B] [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

local instance spatialSceneStandardBorel : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance spatialSceneTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance spatialSceneBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance spatialScenePolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance spatialScenePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance spatialSceneTargetPolish : PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- Different occupied targets in the actual common weak scene have different
spatial coordinates almost surely, derived from the original iid target law. -/
theorem ae_actualRootedCountableScene_spatial_injective
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (ρ : ℕ → Measure (ι → ℝ)) [∀ n, IsProbabilityMeasure (ρ n)]
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ω n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (henv : ∀ n, MeasurePreserving (fun ω ↦ (p n ω, Y n ω)) (P n)
      ((dirichletOne (m n)).prod (Measure.pi (fun _ : Fin (m n + 1) ↦ ν n))))
    (aplus aminus : ∀ n, Ω n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (D : ℕ → Set (ι → ℝ))
    (hν : ∀ n, (ν n).map Prod.fst =
      (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ • volume.restrict (D n))
    (N : ℕ → ℝ) (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hweak : Tendsto (fun n ↦ cavityRootedCountableSceneLaw base (P n) (μ n) (ρ n)
      (p n) (henv n).measurable.fst (aplus n) (aminus n)
      (hplusm n) (hminusm n) (Y n) (hY n) (N n)) atTop (𝓝 Q)) :
    ∀ᵐ (s : CavityCountableTargetScene (A := A) base) ∂(Q : Measure _),
      Set.InjOn Prod.fst (Function.support (LocalConfiguration.multiplicity s.2)) := by
  apply ae_spatial_injective_of_weak_pair_budget Q _ hweak Prod.snd continuous_snd
  intro n j k l
  let R := markedSpatialNearPair (B := B) (Metric.ball (0 : ι → ℝ) ((j : ℝ) + 1))
    (1 / ((k : ℝ) + 1)) (1 / ((l : ℝ) + 1))
  have hR : IsOpen R := isOpen_markedSpatialNearPair Metric.isOpen_ball _ _
  change ((P n).prod (ρ n)).map
    (cavityRootedCountableScene base (μ n) (p n) (aplus n) (aminus n) (Y n) (N n))
      (Prod.snd ⁻¹' {c : LocalConfiguration base | HasPairIn R c}) ≤ _
  rw [Measure.map_apply
    (measurable_cavityRootedCountableScene base (μ n) (p n) (henv n).measurable.fst
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n) (N n))
    ((isOpen_hasPairIn hR).preimage continuous_snd).measurableSet]
  exact measure_cavityRootedTargetConfiguration_nearPair_le base (m n) (P n) (ρ n) (ν n)
    (Y n) (measurePreserving_snd.comp (henv n)) (D n) (hν n)
    Metric.isOpen_ball (by positivity) _

end OTSelector.Probability
