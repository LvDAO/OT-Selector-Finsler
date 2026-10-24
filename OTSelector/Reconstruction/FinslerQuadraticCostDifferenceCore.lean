import OTSelector.Geometry.FinslerQuadraticCostDifferenceRigidity
import OTSelector.Reconstruction.FinslerFiniteCoefficientCores

/-!
# Legal rigidity at an actual frozen population coefficient core

The cost uses the retained reference root, original seed basis and literal
population compliance inverse. Its source mark law is the original conditional
law. The produced coefficient core supplies all legal-pair positivity; original
geometry supplies coefficient measurability.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- The literal frozen original coefficient in the same retained finite label basis. -/
def frozenQuadraticCost (z : Z) :
    ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) →
    ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) → ℝ :=
  Probability.cavitySpatialDifferenceCost (fun s t v ↦ matrixQuadratic
    (populationSeedRootCoefficient (P C.seedIndex).seed a
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker) (z, s, t)) v)

/-- Countable target edges inside the actual retained scalar pair region. -/
def frozenQuadraticLegalDomain {J : Type*}
    (Y : J → (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) :
    Set (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) × J) :=
  {p | (p.1.2, (Y p.2).2) ∈ C.window.region}

variable {J : Type*} [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [BorelSpace E] in
/-- The same retained legal domain is Borel for every countable target enumeration. -/
theorem measurableSet_frozenQuadraticLegalDomain
    (Y : J → (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) :
    MeasurableSet (C.frozenQuadraticLegalDomain Y) :=
  C.window.isCompact_region.measurableSet.preimage
    ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_of_countable (fun j ↦ (Y j).2)).comp measurable_snd))

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instCoreQuadraticMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Original fixed-root matrices give restricted atomlessness with the actual
conditional source marks; no matrix regularity or positivity is assumed anew. -/
theorem nullSingletonClass_map_frozenQuadratic_sub
    {z : Z} (hz : z ∈ C.roots)
    (m : Measure (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
    [m.IsAddHaarMeasure]
    {ρ : Measure ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)}
    (hρ : ρ ≪ m.prod (condDistrib u a η₀ z))
    (Y : J → (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)
    {i j : J} (hij : (Y i).1 ≠ (Y j).1) :
    NullSingletonClass ((ρ.restrict
      (commonLegalSource (C.frozenQuadraticLegalDomain Y) i j)).map
      (fun x ↦ C.frozenQuadraticCost z x (Y i) - C.frozenQuadraticCost z x (Y j))) := by
  apply nullSingletonClass_map_marked_matrixQuadratic_sub m (condDistrib u a η₀ z) hρ
    (fun s t ↦ populationSeedRootCoefficient (P C.seedIndex).seed a
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker) (z, s, t))
    ((measurable_populationSeedRootCoefficient (P C.seedIndex).seed hF hcomplete hu ha hinj
      _).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
    ((measurable_populationSeedRootCoefficient (P C.seedIndex).seed hF hcomplete hu ha hinj
      _).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))) hij
    (measurableSet_commonLegalSource (C.measurableSet_frozenQuadraticLegalDomain Y) i j)
  intro x hx
  exact ⟨C.coefficient_posDef z hz _ hx.1, C.coefficient_posDef z hz _ hx.2⟩

/-- The actual frozen-root local model has at most one same-source plan carried
by a common legally monotone relation with spatially distinct countable targets. -/
theorem frozenQuadratic_plans_eq
    {z : Z} (hz : z ∈ C.roots)
    (m : Measure (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
    [m.IsAddHaarMeasure]
    {ρ : Measure ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)}
    (hρ : ρ ≪ m.prod (condDistrib u a η₀ z))
    (Y : J → (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)
    (hY : Injective (fun j ↦ (Y j).1))
    (Γ : Set (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) × J))
    (hΓ : MeasurableSet Γ) (hsub : Γ ⊆ C.frozenQuadraticLegalDomain Y)
    (π₀ π₁ : Measure (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) × J))
    (hsource₀ : π₀.map Prod.fst = ρ) (hsource₁ : π₁.map Prod.fst = ρ)
    {r : ℝ≥0∞} (hr : r ≠ 0) (hcarried : ∀ᵐ p ∂r • (π₀ + π₁), p ∈ Γ)
    (hcycle : IsTwoCycleMonotoneOn (fun x j ↦ C.frozenQuadraticCost z x (Y j))
      (C.frozenQuadraticLegalDomain Y) Γ) : π₀ = π₁ := by
  apply countable_plans_eq_of_marked_matrixQuadratic_legal_twoCycle
    m (condDistrib u a η₀ z) hρ
    (fun s t ↦ populationSeedRootCoefficient (P C.seedIndex).seed a
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker) (z, s, t)) Y
    (fun _ ↦ (measurable_populationSeedRootCoefficient (P C.seedIndex).seed
      hF hcomplete hu ha hinj _).comp
        (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
    hY (C.frozenQuadraticLegalDomain Y) Γ
    (C.measurableSet_frozenQuadraticLegalDomain Y) hΓ hsub _
    π₀ π₁ hsource₀ hsource₁ hr hcarried hcycle
  intro x j hx
  exact C.coefficient_posDef z hz _ hx

end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
