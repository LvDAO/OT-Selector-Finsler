import OTSelector.Reconstruction.FinslerOriginalClosedWindowClassObservation
import OTSelector.Reconstruction.FinslerOriginalCoordinateHaarPressure

/-! Exact original retained coordinate intensity of every full physical
reference class model, with its genuine native-Haar Jacobian retained. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The physical finite-core intensity is the actual native-Haar atlas
Radon-Nikodym density, without a hidden coordinate-volume normalization. -/
theorem PopulationLocalPressureCore.rootIntensity_eq_populationAtlasTheta
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (z : ℚ → M) :
    D.rootIntensity i z = populationAtlasTheta P a κ (μ.map a)
      (D.haar.continuous.coefficient i).seedIndex z := rfl

/-- A full physical reference model has exactly the original closed-window
mass, thinned by 1-eta and multiplied by its original native-Haar density.
The fine bin count and reference representation do not affect this intensity. -/
theorem PopulationLocalPressureCore.originalWindowReferenceWeights_mass_eq_closed_window
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width)
    (hwindowGap : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed Q j k →
      ∀ x ∈ Q.cell j, ∀ y ∈ Q.cell k,
        x ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        y ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧ x < y)
    {η : ℝ} (hη : η < 1) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    (∑ j, ∑ k, D.originalWindowReferenceWeights γ gap range i ref Q η j k) =
      ((1-η) * D.rootIntensity i ref.val) *
        (D.originalClosedWindowPairKernel hcomplete γ ref.val).real univ := by
  have hz : ref.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,ref.property⟩
  have hgood := (D.haar.continuous.population.good ref.val hz).1
  obtain ⟨π,⟨_hπ,hmap⟩,_⟩ := existsUnique_subtype_coupling_lift hrange hrange
    hgood.2.2.1 hgood.2.2.2 hgood.1
  have hobs := D.originalClosedWindow_class_observation hrange γ i ref π hmap Q
    hwindowGap hfull hη hgap hδ hδ1
  have hm : ((γ ref.val).restrict (D.haar.continuous.coefficient i).window.region).real univ =
      (π.restrict ((Prod.map Subtype.val Subtype.val) ⁻¹'
        (D.haar.continuous.coefficient i).window.region)).real univ := by
    rw [← hobs.2.1]
    exact map_measureReal_apply (measurable_subtype_coe.prodMap measurable_subtype_coe) MeasurableSet.univ
  rw [hobs.2.2.2.2.2,D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i ref.val ref.property,hm]


/-- The SAME coordinate intensity used by the original iid pressure factory
is Theta*(1-eta)*actual retained mass. The canonical Haar Jacobian is explicit. -/
theorem PopulationLocalPressureCore.originalWindowReferenceWeights_coordinate_intensity
    [∀ j, (κ j).IsAddHaarMeasure]
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width)
    (hwindowGap : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed Q j k →
      ∀ x ∈ Q.cell j, ∀ y ∈ Q.cell k,
        x ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        y ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧ x < y)
    {η : ℝ} (hη : η < 1) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    let C := D.haar.continuous.coefficient i
    (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
      (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap range i ref Q η)).real univ =
    ((1-η) * originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex ref.val) *
      (D.originalClosedWindowPairKernel hcomplete γ ref.val).real univ := by
  dsimp only
  have hweights := D.originalWindowReferenceWeights_mass γ gap range i ref Q hη hgap hδ hδ1
  rw [clockClassPairMeasure_real_univ _ hweights.1,
    D.originalWindowReferenceWeights_mass_eq_closed_window hrange γ hcomplete i ref Q
      hwindowGap hfull hη hgap hδ hδ1,
    D.rootIntensity_eq_populationAtlasTheta]
  unfold originalSeedCoordinateIntensity
  ring

end OTSelector.Reconstruction
