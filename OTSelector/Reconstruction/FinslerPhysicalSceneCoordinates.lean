import OTSelector.Reconstruction.FinslerPopulationHaarCellLaws
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation

/-!
# Actual probability laws for physical seed scenes

The source and target laws on a retained cell are the normalized restrictions of
the original physical populations, read in the original seed label and potential
clock.  Their explicit laws keep the original Haar density and conditional clock
kernel.  The same complete seed map recovers the physical laws.  In particular,
no uniform spatial law or independence of the seed label and clock is asserted.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Normalization commutes with a measurable observation, using the actual mass. -/
theorem normalizedFiniteLaw_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f) :
    (normalizedFiniteLaw μ).map f = normalizedFiniteLaw (μ.map f) := by
  have hmass : (μ.map f).real univ = μ.real univ := by
    simp only [measureReal_def, Measure.map_apply hf MeasurableSet.univ, preimage_univ]
  simp only [normalizedFiniteLaw, hmass, Measure.map_smul]

/-- Original almost-everywhere properties persist under finite normalization. -/
theorem ae_normalizedFiniteLaw {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂normalizedFiniteLaw μ, p x :=
  Measure.ae_smul_measure hp _

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

namespace PopulationHaarPressureCore

variable (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- The original seed label together with the original potential clock. -/
def sceneCoordinate (i : Fin D.continuous.count) (x : M) :
    (P (D.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ :=
  (populationSeedRootLabelValue (P (D.continuous.coefficient i).seedIndex).seed a (a x),
    u x)

/-- The actual coordinate probability law on a physical root cell. -/
def sceneLaw (η : Measure M) (i : Fin D.continuous.count) (L : Set (ℚ → M)) :
    Measure ((P (D.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ) :=
  normalizedFiniteLaw ((η.restrict (a ⁻¹' L)).map (D.sceneCoordinate i))

/-- Legal scene points retain their actual root cell and physical carrier. -/
def sceneDomain (i : Fin D.continuous.count) (L : Set (ℚ → M)) (K : Set M) :
    Set ((P (D.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ) :=
  {s | s.1 ∈ populationSeedRootLabelValue
      (P (D.continuous.coefficient i).seedIndex).seed a '' L ∧
    populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s ∈ K}

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSceneMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The coordinate observation is measurable for the original Finsler atlas. -/
theorem measurable_sceneCoordinate (i : Fin D.continuous.count) :
    Measurable (D.sceneCoordinate i) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  exact ((measurable_populationSeedRootLabelValue _ hF hcomplete hu ha hinj).comp ha).prodMk
    hu.continuous.measurable

/-- Both scene laws are exactly normalized original Haar-clock laws. -/
theorem sceneLaw_eq_original_laws
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let intensity := ((κ C.seedIndex).restrict (populationSeedRootLabelValue S a '' L)).withDensity
      (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)
    D.sceneLaw η₀ i L = normalizedFiniteLaw
        (intensity ⊗ₘ populationSeedCoordinateClockKernel S a ha (condDistrib u a η₀)) ∧
      D.sceneLaw η₁ i L = normalizedFiniteLaw
        (intensity ⊗ₘ populationSeedCoordinateClockKernel S a ha (condDistrib u a η₁)) := by
  obtain ⟨hs, ht⟩ := D.cell_joint_laws hF hcomplete hu ha hinj i hL hsub
  exact ⟨congrArg normalizedFiniteLaw hs, congrArg normalizedFiniteLaw ht⟩

/-- The normalized physical restrictions produce the same coordinate laws. -/
theorem map_normalized_physical_eq_sceneLaw (η : Measure M)
    (i : Fin D.continuous.count) (L : Set (ℚ → M)) :
    (normalizedFiniteLaw (η.restrict (a ⁻¹' L))).map (D.sceneCoordinate i) =
      D.sceneLaw η i L :=
  normalizedFiniteLaw_map _ _ (D.measurable_sceneCoordinate hF hcomplete hu ha hinj i)

/-- Every retained cell of positive original root mass gives two probability laws. -/
theorem sceneLaw_probability
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) (hmass : 0 < lambda.real L) :
    IsProbabilityMeasure (D.sceneLaw η₀ i L) ∧
      IsProbabilityMeasure (D.sceneLaw η₁ i L) := by
  have hcoord := D.measurable_sceneCoordinate hF hcomplete hu ha hinj i
  obtain ⟨_, hs, ht⟩ := D.cell_masses hF hcomplete hu ha hinj i hL hsub
  have hpositive (η : Measure M) (he : η (a ⁻¹' L) = lambda L) :
      0 < ((η.restrict (a ⁻¹' L)).map (D.sceneCoordinate i)).real univ := by
    simpa only [measureReal_def, Measure.map_apply hcoord MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, he] using hmass
  exact ⟨normalizedFiniteLaw_probability _ (hpositive η₀ hs),
    normalizedFiniteLaw_probability _ (hpositive η₁ ht)⟩

/-- The legal domain is measurable; it uses the actual seed and physical carrier. -/
theorem measurableSet_sceneDomain
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots)
    {K : Set M} (hK : MeasurableSet K) : MeasurableSet (D.sceneDomain i L K) := by
  exact ((D.measurable_cell_label_image hcomplete i hL hsub).preimage measurable_fst).inter
    (hK.preimage (measurable_populationSeedPhysicalMap _))

/-- Every coordinate scene point is almost surely in the same retained root cell. -/
theorem sceneLaw_ae_label_mem (η : Measure M)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    ∀ᵐ s ∂D.sceneLaw η i L, s.1 ∈ populationSeedRootLabelValue
      (P (D.continuous.coefficient i).seedIndex).seed a '' L := by
  apply ae_normalizedFiniteLaw
  apply (ae_map_iff (D.measurable_sceneCoordinate hF hcomplete hu ha hinj i).aemeasurable
    ((D.measurable_cell_label_image hcomplete i hL hsub).preimage measurable_fst)).mpr
  filter_upwards [ae_restrict_mem (hL.preimage ha)] with x hx
  exact mem_image_of_mem _ hx

variable
  (horder : let _instSceneOrder : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
  (hb : Measurable b)
  (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
  (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
  (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)

include horder hb hinv hη₀reg hη₁reg

/-- The complete seed reconstruction inverts the observation on both original
physical restrictions, before taking any coordinate law. -/
theorem physical_sceneCoordinate_inverse_ae
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    (∀ᵐ x ∂normalizedFiniteLaw (η₀.restrict (a ⁻¹' L)),
      populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed
        (D.sceneCoordinate i x) = x) ∧
      (∀ᵐ x ∂normalizedFiniteLaw (η₁.restrict (a ⁻¹' L)),
        populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed
          (D.sceneCoordinate i x) = x) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  let C := D.continuous.coefficient i
  let S := (P C.seedIndex).seed
  obtain ⟨hs, ht⟩ := D.physical_endpoints_ae hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg
  have hpoint (x : M) (hx : a x ∈ L)
      (he : ∀ j : Fin D.continuous.count,
        a x ∈ (D.continuous.coefficient j).roots →
        x = (P (D.continuous.coefficient j).seedIndex).seed.curve
          (populationSeedRootLabelValue (P (D.continuous.coefficient j).seedIndex).seed a
            (a x)) (u x - (P (D.continuous.coefficient j).seedIndex).seed.level)) :
      populationSeedPhysicalMap S (D.sceneCoordinate i x) = x := by
    change populationSeedPhysicalMap S (populationSeedRootLabelValue S a (a x), u x) = x
    have hxpiece := C.roots_subset_piece (hsub hx)
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
      ⟨a x, hxpiece⟩, populationSeedPhysicalMap_at_label]
    simpa only [C, S, populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj
      C.seedIndex ⟨a x, hxpiece⟩] using (he i (hsub hx)).symm
  constructor
  · apply ae_normalizedFiniteLaw
    filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem (hL.preimage ha)] with x he hx
    exact hpoint x hx he
  · apply ae_normalizedFiniteLaw
    filter_upwards [ae_restrict_of_ae ht, ae_restrict_mem (hL.preimage ha)] with x he hx
    exact hpoint x hx he

/-- The original observation inverts reconstruction almost everywhere in either
actual scene law.  This supplies the actual injective legal coordinate carrier. -/
theorem sceneCoordinate_physical_inverse_ae
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    (∀ᵐ s ∂D.sceneLaw η₀ i L,
      D.sceneCoordinate i
        (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s) = s) ∧
      (∀ᵐ s ∂D.sceneLaw η₁ i L,
        D.sceneCoordinate i
          (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s) = s) := by
  have hq := D.measurable_sceneCoordinate hF hcomplete hu ha hinj i
  have hf := measurable_populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed
  obtain ⟨hs, ht⟩ := D.physical_sceneCoordinate_inverse_ae hF hcomplete hu ha hinj
    horder hb hinv hη₀reg hη₁reg i hL hsub
  have hcolor (η : Measure M) (he : ∀ᵐ x ∂normalizedFiniteLaw (η.restrict (a ⁻¹' L)),
      populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed
        (D.sceneCoordinate i x) = x) :
      ∀ᵐ s ∂D.sceneLaw η i L,
        D.sceneCoordinate i
          (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s) = s := by
    rw [← D.map_normalized_physical_eq_sceneLaw hF hcomplete hu ha hinj η i L]
    apply (ae_map_iff hq.aemeasurable
      (measurableSet_eq_fun (hq.comp hf) measurable_id)).mpr
    exact he.mono fun x hx ↦ congrArg (D.sceneCoordinate i) hx
  exact ⟨hcolor η₀ hs, hcolor η₁ ht⟩

/-- Both actual scene laws reconstruct the normalized original physical colors. -/
theorem sceneLaw_physical_recovery
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    (D.sceneLaw η₀ i L).map
        (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed) =
        normalizedFiniteLaw (η₀.restrict (a ⁻¹' L)) ∧
      (D.sceneLaw η₁ i L).map
        (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed) =
        normalizedFiniteLaw (η₁.restrict (a ⁻¹' L)) := by
  obtain ⟨hs, ht⟩ := D.sceneLaw_eq_original_laws hF hcomplete hu ha hinj i hL hsub
  obtain ⟨hps, hpt⟩ := D.physical_cell_laws hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg i hL hsub
  constructor
  · rw [hs, normalizedFiniteLaw_map _ _ (measurable_populationSeedPhysicalMap _), hps]
  · rw [ht, normalizedFiniteLaw_map _ _ (measurable_populationSeedPhysicalMap _), hpt]

/-- Original physical carriers give the actual legal domains of both scene laws. -/
theorem sceneLaw_ae_domain
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots)
    {A B : Set M}
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ x ∂η₁, x ∈ B) :
    (∀ᵐ s ∂D.sceneLaw η₀ i L, s ∈ D.sceneDomain i L A) ∧
      (∀ᵐ s ∂D.sceneLaw η₁ i L, s ∈ D.sceneDomain i L B) := by
  obtain ⟨hs, ht⟩ := D.sceneLaw_physical_recovery hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg i hL hsub
  have hsrc : ∀ᵐ s ∂D.sceneLaw η₀ i L,
      populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s ∈ A := by
    apply ae_of_ae_map (measurable_populationSeedPhysicalMap _).aemeasurable
    rw [hs]
    exact ae_normalizedFiniteLaw (ae_restrict_of_ae hη₀A)
  have htrg : ∀ᵐ s ∂D.sceneLaw η₁ i L,
      populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s ∈ B := by
    apply ae_of_ae_map (measurable_populationSeedPhysicalMap _).aemeasurable
    rw [ht]
    exact ae_normalizedFiniteLaw (ae_restrict_of_ae hη₁B)
  exact ⟨(D.sceneLaw_ae_label_mem hF hcomplete hu ha hinj η₀ i hL hsub).and hsrc,
    (D.sceneLaw_ae_label_mem hF hcomplete hu ha hinj η₁ i hL hsub).and htrg⟩

end PopulationHaarPressureCore
end OTSelector.Reconstruction
