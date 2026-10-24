import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicUnionCoreIsolation

/-!
# Actual retained near edges enter the selected endpoint carrier product

The retained event is the full original near-event union intersected with the
given physical carriers. Its observed edges enter the selected core product
inside the selected macroscopic label window and a bounded source-root window.
This supplies the event-local inclusion needed by the full/core witness loss.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- The full retained original near-event union, on the same physical carriers. -/
def retainedNearCarrierEvent (A B : Set M) (nearRadius : ℝ) : Set (M × M) :=
  (⋃ k, D.nearDisplacementEvent k nearRadius) ∩ (A ×ˢ B)

/-- Both original endpoints lie in the selected original root core and their
respective physical carrier. -/
def selectedCoreCarrierProduct (i : Fin D.haar.continuous.count) (A B : Set M) :
    Set (M × M) :=
  (a ⁻¹' (D.haar.continuous.coefficient i).roots ∩ A) ×ˢ
    (a ⁻¹' (D.haar.continuous.coefficient i).roots ∩ B)

/-- The literal finite coordinate space of the selected original seed basis. -/
abbrev coreSpatialCoordinateSpace (i : Fin D.haar.continuous.count) :=
  Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ

/-- The original label in the selected original seed frame. -/
def coreMacroLabel (i : Fin D.haar.continuous.count) (z : ℚ → M) :
    D.coreSpatialCoordinateSpace i :=
  (Module.finBasis ℝ
    (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFun
      (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a z)

/-- The open macroscopic window around the full original compact core label image. -/
def coreMacroLabelWindow (i : Fin D.haar.continuous.count) (radius : ℝ) :
    Set (D.coreSpatialCoordinateSpace i) :=
  ⋃ z ∈ (D.haar.continuous.coefficient i).roots,
    Metric.ball (D.coreMacroLabel i z) radius

theorem isOpen_coreMacroLabelWindow (i : Fin D.haar.continuous.count) (radius : ℝ) :
    IsOpen (D.coreMacroLabelWindow i radius) :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- Every condition defining the actual retained near event remains measurable. -/
theorem measurableSet_retainedNearCarrierEvent
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B) (nearRadius : ℝ) :
    MeasurableSet (D.retainedNearCarrierEvent A B nearRadius) :=
  (MeasurableSet.iUnion fun k ↦
    D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj k nearRadius).inter
      (hA.prod hB)

/-- The selected physical endpoint carrier product is measurable in the original space. -/
theorem measurableSet_selectedCoreCarrierProduct
    (i : Fin D.haar.continuous.count) {A B : Set M}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (D.selectedCoreCarrierProduct i A B) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hroot := (D.haar.continuous.coefficient i).roots_compact.measurableSet.preimage ha
  exact (hroot.inter hA).prod (hroot.inter hB)

/-- This is the literal event inclusion for the rooted full/core witness loss.
Only the source spatial norms of the two observation tests are bounded. The
entire original near-event union is retained before the selected core is identified. -/
theorem exists_rooted_retainedNearCarrier_inclusion_selectedCoreProduct
    (i : Fin D.haar.continuous.count)
    (A B : Set M) (R nearRadius : ℝ)
    : ∃ radius > 0, ∃ threshold > 0,
      ∀ T₀ T₁ : Set (((D.coreSpatialCoordinateSpace i) × ℝ) ×
        ((D.coreSpatialCoordinateSpace i) × ℝ)),
      (∀ q ∈ T₀ ∪ T₁, ‖q.1.1‖ ≤ R) →
      ∀ scale : ℝ, threshold ≤ scale →
      ∀ root : D.coreSpatialCoordinateSpace i,
        scale⁻¹ • root ∈ D.coreMacroLabelWindow i radius →
      ∀ e ∈ D.retainedNearCarrierEvent A B nearRadius ∩
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
          (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex ×ˢ univ),
        physicalSceneRootedObservation
          (physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
            (D.haar.continuous.coefficient i).seedIndex scale) u root e ∈ T₀ ∪ T₁ →
        e ∈ D.selectedCoreCarrierProduct i A B := by
  let C := D.haar.continuous.coefficient i
  obtain ⟨radius, hradius, hisolate⟩ :=
    D.exists_fixed_seed_macro_retained_near_core_isolation hF hcomplete hu ha hinj i
      C.roots_compact (Subset.rfl : C.roots ⊆ C.roots)
  obtain ⟨threshold, hthreshold, hisolate⟩ := hisolate R
  refine ⟨radius, hradius, threshold, hthreshold, ?_⟩
  intro T₀ T₁ hsource scale hs root hmacro e he hobs
  obtain ⟨z, hz, hzmacro⟩ := Set.mem_iUnion₂.mp hmacro
  have hmacro' : ∃ z ∈ C.roots, dist (scale⁻¹ • root)
      ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
        (populationSeedRootLabelValue (P C.seedIndex).seed a z)) < radius :=
    ⟨z, hz, Metric.mem_ball.mp hzmacro⟩
  have hR : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale e.1 - root‖ ≤ R := hsource _ hobs
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp he.1.1
  have hki : k = i := hisolate scale hs root hmacro' k nearRadius e hk he.2.1 hR
  subst k
  exact ⟨⟨hk.1, he.1.2.1⟩, ⟨hk.2.1, he.1.2.2⟩⟩

/-- Every ball around a specified actual core label uses the same positive
isolation radius and scale threshold as the full compact-image window. -/
theorem exists_rooted_retainedNearCarrier_inclusion_selectedCoreProduct_on_ball
    (i : Fin D.haar.continuous.count)
    (A B : Set M) (R nearRadius : ℝ)
    : ∃ radius > 0, ∃ threshold > 0,
      ∀ T₀ T₁ : Set (((D.coreSpatialCoordinateSpace i) × ℝ) ×
        ((D.coreSpatialCoordinateSpace i) × ℝ)),
      (∀ q ∈ T₀ ∪ T₁, ‖q.1.1‖ ≤ R) →
      ∀ z₀ ∈ (D.haar.continuous.coefficient i).roots,
      ∀ scale : ℝ, threshold ≤ scale →
      ∀ root : D.coreSpatialCoordinateSpace i,
        dist (scale⁻¹ • root) (D.coreMacroLabel i z₀) < radius →
      ∀ e ∈ D.retainedNearCarrierEvent A B nearRadius ∩
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
          (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex ×ˢ univ),
        physicalSceneRootedObservation
          (physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
            (D.haar.continuous.coefficient i).seedIndex scale) u root e ∈ T₀ ∪ T₁ →
        e ∈ D.selectedCoreCarrierProduct i A B := by
  obtain ⟨radius, hradius, threshold, hthreshold, hinc⟩ :=
    D.exists_rooted_retainedNearCarrier_inclusion_selectedCoreProduct
      hF hcomplete hu ha hinj i A B R nearRadius
  refine ⟨radius, hradius, threshold, hthreshold, ?_⟩
  intro T₀ T₁ hsource z₀ hz₀ scale hs root hmacro e he hobs
  exact hinc T₀ T₁ hsource scale hs root
    (Set.mem_iUnion₂.mpr ⟨z₀, hz₀, Metric.mem_ball.mpr hmacro⟩) e he hobs

end PopulationLocalPressureCore
end OTSelector.Reconstruction
