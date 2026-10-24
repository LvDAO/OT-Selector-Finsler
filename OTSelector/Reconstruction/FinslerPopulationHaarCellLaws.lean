import OTSelector.Reconstruction.FinslerPopulationSeedPhysicalRecovery

/-!
# Original Haar-clock laws on measurable pressure cells

Every measurable subcell of a retained root core keeps the same original Haar
intensity and both original conditional clock kernels. The actual seed position
map recovers the original physical restriction on that cell.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- An exact joint law on a measurable root region restricts to every smaller
measurable root region without changing its conditional kernel. -/
theorem original_label_clock_joint_on_subset
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {η : Measure X} [IsFiniteMeasure η] {lambda : Measure Z} [SFinite lambda]
    {a : X → Z} {u : X → ℝ} (ha : Measurable a) (hu : Measurable u)
    {H K : Set Z} (hK : MeasurableSet K) (hsub : K ⊆ H)
    (hjoint : (η.restrict (a ⁻¹' H)).map (fun x ↦ (a x, u x)) =
      lambda.restrict H ⊗ₘ condDistrib u a η) :
    (η.restrict (a ⁻¹' K)).map (fun x ↦ (a x, u x)) =
      lambda.restrict K ⊗ₘ condDistrib u a η := by
  have h := congrArg (fun μ : Measure (Z × ℝ) ↦ μ.restrict (K ×ˢ univ)) hjoint
  rw [Measure.restrict_map (ha.prodMk hu) (hK.prod MeasurableSet.univ),
    ← restrict_label_compProd (lambda.restrict H) (condDistrib u a η) hK] at h
  have hpre : (fun x ↦ (a x, u x)) ⁻¹' (K ×ˢ univ) = a ⁻¹' K := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, and_true]
  rw [hpre, Measure.restrict_restrict_of_subset (preimage_mono hsub),
    Measure.restrict_restrict_of_subset hsub] at h
  exact h

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

variable {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
  (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instCellMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu hinj

/-- Each measurable subcell retains the original Haar intensity and the two
unchanged original conditional clock kernels. -/
theorem PopulationHaarPressureCore.cell_joint_laws
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let intensity := ((κ C.seedIndex).restrict (R '' L)).withDensity
      (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)
    (η₀.restrict (a ⁻¹' L)).map (fun x ↦ (R (a x), u x)) =
        intensity ⊗ₘ populationSeedCoordinateClockKernel S a ha (condDistrib u a η₀) ∧
    (η₁.restrict (a ⁻¹' L)).map (fun x ↦ (R (a x), u x)) =
        intensity ⊗ₘ populationSeedCoordinateClockKernel S a ha (condDistrib u a η₁) := by
  let _instCellMetric : MetricSpace M := F.metricSpace
  let _instCellProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instCellPolish : PolishSpace M := inferInstance
  let _instCellBorel : BorelSpace (ℚ → M) := inferInstance
  exact ⟨original_seed_core_joint_eq_compProd_of_joint P a κ lambda
      hF hcomplete hu ha hinj η₀ (D.continuous.coefficient i).seedIndex hL
      (hsub.trans (D.continuous.coefficient i).roots_subset_piece)
      (original_label_clock_joint_on_subset ha hu.continuous.measurable hL hsub
        (D.continuous.recovery.source_joint i)),
    original_seed_core_joint_eq_compProd_of_joint P a κ lambda
      hF hcomplete hu ha hinj η₁ (D.continuous.coefficient i).seedIndex hL
      (hsub.trans (D.continuous.coefficient i).roots_subset_piece)
      (original_label_clock_joint_on_subset ha hu.continuous.measurable hL hsub
        (D.continuous.recovery.target_joint i))⟩

omit hF hu hinj [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] in
/-- Every measurable retained root cell has a measurable image in the actual
seed labels; the stored root identity supplies injectivity. -/
theorem PopulationHaarPressureCore.measurable_cell_label_image
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    MeasurableSet (populationSeedRootLabelValue
      (P (D.continuous.coefficient i).seedIndex).seed a '' L) := by
  let _instCellMetric : MetricSpace M := F.metricSpace
  let _instCellProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instCellPolish : PolishSpace M := inferInstance
  let _instCellBorel : BorelSpace (ℚ → M) := inferInstance
  have hsub' : L ⊆ (D.intensity i).roots := by
    rwa [D.intensity_roots]
  apply hL.image_of_continuousOn_injOn ((D.intensity i).continuous_label.mono hsub')
  intro z hz z' hz' he
  calc
    z = a ((P (D.continuous.coefficient i).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (D.continuous.coefficient i).seedIndex).seed a z) 0) :=
      ((D.intensity i).root_identity z (hsub' hz)).symm
    _ = z' := by rw [he]; exact (D.intensity i).root_identity z' (hsub' hz')

include ha in
/-- A retained measurable cell has the same original mass in seed Haar
coordinates and in both physical populations. -/
theorem PopulationHaarPressureCore.cell_masses
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let intensity := ((κ C.seedIndex).restrict (R '' L)).withDensity
      (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)
    intensity univ = lambda L ∧ η₀ (a ⁻¹' L) = lambda L ∧ η₁ (a ⁻¹' L) = lambda L := by
  let _instCellMetric : MetricSpace M := F.metricSpace
  let _instCellProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instCellPolish : PolishSpace M := inferInstance
  let _instCellBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let intensity := ((κ C.seedIndex).restrict (R '' L)).withDensity
    (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)
  have he : (lambda.restrict L).map R = intensity :=
    map_populationSeedCore_eq_withDensity P a κ lambda hF hcomplete hu ha hinj
      C.seedIndex hL (hsub.trans C.roots_subset_piece)
  have hm : intensity univ = lambda L := by
    rw [← he]
    exact populationSeedCoreCoordinateLaw_mass P a lambda hF hcomplete hu ha hinj C.seedIndex L
  let _instCellIntensityFinite : IsFiniteMeasure intensity := by
    rw [← he]
    infer_instance
  have hcoord : Measurable (fun x ↦ (R (a x), u x)) :=
    ((measurable_populationSeedRootLabelValue _ hF hcomplete hu ha hinj).comp ha).prodMk
      hu.continuous.measurable
  obtain ⟨hsource, htarget⟩ := D.cell_joint_laws hF hcomplete hu ha hinj i hL hsub
  have hs := congrArg (fun μ : Measure ((P C.seedIndex).seed.covector.ker × ℝ) ↦ μ univ) hsource
  have ht := congrArg (fun μ : Measure ((P C.seedIndex).seed.covector.ker × ℝ) ↦ μ univ) htarget
  change (η₀.restrict (a ⁻¹' L)).map (fun x ↦ (R (a x), u x)) univ =
    (intensity ⊗ₘ populationSeedCoordinateClockKernel (P C.seedIndex).seed a ha
      (condDistrib u a η₀)) univ at hs
  change (η₁.restrict (a ⁻¹' L)).map (fun x ↦ (R (a x), u x)) univ =
    (intensity ⊗ₘ populationSeedCoordinateClockKernel (P C.seedIndex).seed a ha
      (condDistrib u a η₁)) univ at ht
  simp only [Measure.map_apply hcoord MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, Measure.compProd_apply_univ] at hs ht
  exact ⟨hm, hs.trans hm, ht.trans hm⟩

include ha in
/-- The stored positive finite intensity bounds compare every subcell's original
root mass directly with its actual Haar volume. -/
theorem PopulationHaarPressureCore.cell_haar_mass_bounds
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    let C := D.continuous.coefficient i
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    ENNReal.ofReal (D.intensity i).lower * (κ C.seedIndex) (R '' L) ≤ lambda L ∧
      lambda L ≤ ENNReal.ofReal (D.intensity i).upper * (κ C.seedIndex) (R '' L) := by
  let _instCellMetric : MetricSpace M := F.metricSpace
  let _instCellProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instCellPolish : PolishSpace M := inferInstance
  let _instCellBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let d := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  let m := (κ C.seedIndex).restrict (R '' L)
  have hsub' : L ⊆ (D.intensity i).roots := by rwa [D.intensity_roots]
  have himage : MeasurableSet (R '' L) := D.measurable_cell_label_image hcomplete i hL hsub
  have hfinite (w) (hw : w ∈ R '' L) : d w ≠ (∞ : ℝ≥0∞) := by
    obtain ⟨z, hz, rfl⟩ := hw
    rw [show d (R z) = populationSeedPieceRootDensity P a κ lambda C.seedIndex z from
      populationSeedPieceHaarDensity_at_root P a κ lambda hF hcomplete hu ha hinj
        C.seedIndex (C.roots_subset_piece (hsub hz))]
    exact ((D.intensity i).finite_density z (hsub' hz)).ne
  have hlow : (fun _ ↦ ENNReal.ofReal (D.intensity i).lower) ≤ᵐ[m] d := by
    filter_upwards [ae_restrict_mem himage] with w hw
    exact (ENNReal.ofReal_le_ofReal
      ((D.intensity i).bounds w (image_mono hsub' hw)).1).trans ENNReal.ofReal_toReal_le
  have hupp : d ≤ᵐ[m] (fun _ ↦ ENNReal.ofReal (D.intensity i).upper) := by
    filter_upwards [ae_restrict_mem himage] with w hw
    rw [← ENNReal.ofReal_toReal (hfinite w hw)]
    exact ENNReal.ofReal_le_ofReal ((D.intensity i).bounds w (image_mono hsub' hw)).2
  have hm : m.withDensity d univ = lambda L :=
    (D.cell_masses hF hcomplete hu ha hinj i hL hsub).1
  have hlo := (withDensity_mono hlow) univ
  have hhi := (withDensity_mono hupp) univ
  simp only [withDensity_const, Measure.smul_apply, smul_eq_mul, hm] at hlo hhi
  simpa only [m, Measure.restrict_apply_univ] using And.intro hlo hhi

/-- Measurable pressure cells reconstruct their original physical colors through
the same actual complete seed map, without changing any intensity or kernel. -/
theorem PopulationHaarPressureCore.physical_cell_laws
    (horder : let _instCellOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let intensity := ((κ C.seedIndex).restrict (R '' L)).withDensity
      (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)
    (intensity ⊗ₘ populationSeedCoordinateClockKernel S a ha
      (condDistrib u a η₀)).map (populationSeedPhysicalMap S) = η₀.restrict (a ⁻¹' L) ∧
    (intensity ⊗ₘ populationSeedCoordinateClockKernel S a ha
      (condDistrib u a η₁)).map (populationSeedPhysicalMap S) = η₁.restrict (a ⁻¹' L) := by
  let _instCellMetric : MetricSpace M := F.metricSpace
  let _instCellProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instCellPolish : PolishSpace M := inferInstance
  let _instCellBorel : BorelSpace (ℚ → M) := inferInstance
  exact ⟨original_seed_core_physical_recovery_of_joint P a κ lambda
      hF hcomplete hu ha hinj η₀ hb (hη₀reg.mono fun x hx ↦ hinv x hx)
      (D.continuous.coefficient i).seedIndex hL
      (hsub.trans (D.continuous.coefficient i).roots_subset_piece)
      (original_label_clock_joint_on_subset ha hu.continuous.measurable hL hsub
        (D.continuous.recovery.source_joint i))
      (fun z hz ↦ (D.original_inverse_ae hF hcomplete hu ha hinj horder hinv i (hsub hz)).1),
    original_seed_core_physical_recovery_of_joint P a κ lambda
      hF hcomplete hu ha hinj η₁ hb (hη₁reg.mono fun x hx ↦ hinv x hx)
      (D.continuous.coefficient i).seedIndex hL
      (hsub.trans (D.continuous.coefficient i).roots_subset_piece)
      (original_label_clock_joint_on_subset ha hu.continuous.measurable hL hsub
        (D.continuous.recovery.target_joint i))
      (fun z hz ↦ (D.original_inverse_ae hF hcomplete hu ha hinj horder hinv i (hsub hz)).2)⟩

end OTSelector.Reconstruction
