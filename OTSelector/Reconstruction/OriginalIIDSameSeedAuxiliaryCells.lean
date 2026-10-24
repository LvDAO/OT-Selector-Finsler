import OTSelector.Reconstruction.OriginalIIDActualKineticClosure

/-!
# Same original seed across auxiliary accuracy cells

Auxiliary cells are always sets in the old seed's original coordinate space.
A cell with a different auxiliary seed is empty. The remaining finite index
subtype records the literal seed equality; its transports reduce to identity
and preserve the original label, physical mask, scaled coordinate and raw
matrix cost. No sample subsequence or scene candidate is selected here.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The original fixed-basis coordinate type of a seed, without auxiliary data. -/
abbrev OriginalIIDSeedCoordinateSpace (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :=
  Fin (finrank ℝ (P j).seed.covector.ker) → ℝ

/-- Transport between literally equal original seed indices. -/
def originalIIDSeedCoordinateCast {j k : ℕ} (h : j = k)
    (c : OriginalIIDSeedCoordinateSpace P j) : OriginalIIDSeedCoordinateSpace P k :=
  cast (congrArg (OriginalIIDSeedCoordinateSpace P) h) c

@[simp] theorem originalIIDSeedCoordinateCast_rfl (j : ℕ)
    (c : OriginalIIDSeedCoordinateSpace P j) :
    originalIIDSeedCoordinateCast (P := P) (rfl : j = j) c = c := rfl

/-- The seed coordinate transport introduces no new coordinate value. -/
theorem originalIIDSeedCoordinateCast_heq {j k : ℕ} (h : j = k)
    (c : OriginalIIDSeedCoordinateSpace P j) :
    HEq (originalIIDSeedCoordinateCast (P := P) h c) c :=
  cast_heq _ _

/-- Equal original seed indices have the same transverse dimension. -/
theorem originalIID_seed_finrank_eq {j k : ℕ} (h : j = k) :
    finrank ℝ (P j).seed.covector.ker = finrank ℝ (P k).seed.covector.ker := by
  cases h
  rfl

/-- The macro label is exactly the same original label after seed transport. -/
theorem originalIIDSeedCoordinateCast_macroLabel {j k : ℕ} (h : j = k)
    (z : ℚ → M) :
    originalIIDSeedCoordinateCast (P := P) h
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z) =
      physicalSceneOriginalMacroLabel (P := P) (a := a) k z := by
  cases h
  rfl

/-- Images of any root set agree in the same original seed coordinates. -/
theorem originalIIDSeedCoordinateCast_macroLabel_image {j k : ℕ} (h : j = k)
    (A : Set (ℚ → M)) :
    originalIIDSeedCoordinateCast (P := P) h ''
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j '' A) =
      physicalSceneOriginalMacroLabel (P := P) (a := a) k '' A := by
  cases h
  simp only [originalIIDSeedCoordinateCast_rfl, image_id']

/-- The source mask is the same physical seed piece, independently of the core. -/
theorem physicalSceneOriginalSeedSource_eq_of_seed_eq {j k : ℕ} (h : j = k) :
    physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j =
      physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) k := by
  cases h
  rfl

/-- Every actual scaled physical coordinate uses the same original seed basis. -/
theorem originalIIDSeedCoordinateCast_scaledPosition {j k : ℕ} (h : j = k)
    (s : ℝ) (x : M) :
    originalIIDSeedCoordinateCast (P := P) h
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j s x) =
      physicalSceneOriginalSeedScaledPosition (P := P) (a := a) k s x := by
  cases h
  rfl

/-- The total original root readout is unchanged by equality of seed indices. -/
theorem originalIIDSeedCoordinateCast_macroRootValue {j k : ℕ} (h : j = k)
    (c : OriginalIIDSeedCoordinateSpace P j) :
    physicalSceneOriginalMacroRootValue (P := P) (a := a) k
        (originalIIDSeedCoordinateCast (P := P) h c) =
      physicalSceneOriginalMacroRootValue (P := P) (a := a) j c := by
  cases h
  rfl

/-- The complete raw macro matrix is the same actual matrix, with only its
finite index type transported along the original seed equality. -/
theorem originalIIDSeedCoordinateCast_macroCoefficient_heq {j k : ℕ} (h : j = k)
    (c : OriginalIIDSeedCoordinateSpace P j) (clocks : ℝ × ℝ) :
    HEq (physicalSceneOriginalMacroCoefficient (P := P) (a := a) k
      (originalIIDSeedCoordinateCast (P := P) h c, clocks))
      (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c, clocks)) := by
  cases h
  rfl

/-- Scalar raw energy is literally unchanged, so its target type needs no cast. -/
theorem originalIIDSeedCoordinateCast_raw_matrixQuadratic {j k : ℕ} (h : j = k)
    (c v : OriginalIIDSeedCoordinateSpace P j) (clocks : ℝ × ℝ) :
    matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a) k
        (originalIIDSeedCoordinateCast (P := P) h c, clocks))
      (originalIIDSeedCoordinateCast (P := P) h v) =
    matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c, clocks)) v := by
  cases h
  rfl

variable {δ₀ δ₁ : ℝ≥0∞}

/-- The literal auxiliary intersection, always in the old fixed seed coordinates. -/
def originalIIDAuxiliaryCell
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (C' : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₁) :
    Set (OriginalIIDSeedCoordinateSpace P C.seedIndex) :=
  physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' (C.roots ∩ C'.roots)

/-- This is exactly the two-image cell used by original root-mass recovery. -/
theorem originalIIDAuxiliaryCell_eq_basis_image
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (C' : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₁) :
    originalIIDAuxiliaryCell C C' =
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL ''
        (populationSeedRootLabelValue (P C.seedIndex).seed a '' (C.roots ∩ C'.roots)) := by
  rw [image_image]
  rfl

/-- Nonempty actual auxiliary cells identify the original seed exactly. -/
theorem originalIIDAuxiliaryCell_seed_eq_of_mem
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (C' : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₁)
    {c : OriginalIIDSeedCoordinateSpace P C.seedIndex} (hc : c ∈ originalIIDAuxiliaryCell C C') :
    C'.seedIndex = C.seedIndex := by
  obtain ⟨z, hz, _⟩ := hc
  exact (original_seedIndex_eq_of_common_root C C' hz.1 hz.2).symm

/-- Auxiliary cores with another original seed contribute the empty cell. -/
theorem originalIIDAuxiliaryCell_eq_empty_of_seed_ne
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (C' : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₁)
    (hne : C'.seedIndex ≠ C.seedIndex) : originalIIDAuxiliaryCell C C' = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  exact hne (originalIIDAuxiliaryCell_seed_eq_of_mem C C' hc)

/-- In the same seed, the old-coordinate cell is exactly the transported
auxiliary-coordinate image of its actual root intersection. -/
theorem originalIIDAuxiliaryCell_eq_cast_aux_image
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (C' : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₁)
    (hseed : C'.seedIndex = C.seedIndex) :
    originalIIDAuxiliaryCell C C' =
      originalIIDSeedCoordinateCast (P := P) hseed ''
        (physicalSceneOriginalMacroLabel (P := P) (a := a) C'.seedIndex ''
          (C.roots ∩ C'.roots)) := by
  rw [originalIIDSeedCoordinateCast_macroLabel_image]
  rfl

/-- The actual old-coordinate cell lies in the transported auxiliary macro core. -/
theorem originalIIDAuxiliaryCell_subset_cast_aux_core
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (C' : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₁)
    (hseed : C'.seedIndex = C.seedIndex) :
    originalIIDAuxiliaryCell C C' ⊆
      originalIIDSeedCoordinateCast (P := P) hseed ''
        (physicalSceneOriginalMacroLabel (P := P) (a := a) C'.seedIndex '' C'.roots) := by
  rw [originalIIDAuxiliaryCell_eq_cast_aux_image C C' hseed]
  exact image_mono (image_mono inter_subset_right)

variable {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The original core macro label has the same fixed-seed transport identity. -/
theorem PopulationLocalPressureCore.coreMacroLabel_cast_eq
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {j : ℕ}
    (hseed : (D.haar.continuous.coefficient i).seedIndex = j) (z : ℚ → M) :
    originalIIDSeedCoordinateCast (P := P) hseed (D.coreMacroLabel i z) =
      physicalSceneOriginalMacroLabel (P := P) (a := a) j z := by
  exact originalIIDSeedCoordinateCast_macroLabel hseed z

/-- The finite auxiliary indices that actually use the old original seed. -/
abbrev OriginalIIDSameSeedAuxiliaryIndex
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss) :=
  {i : Fin D.continuous.count // (D.continuous.coefficient i).seedIndex = C.seedIndex}

/-- Filtering by the true seed equality changes no root-coordinate cell union. -/
theorem iUnion_originalIIDAuxiliaryCell_eq_same_seed
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss) :
    (⋃ i : Fin D.continuous.count, originalIIDAuxiliaryCell C (D.continuous.coefficient i)) =
      ⋃ i : OriginalIIDSameSeedAuxiliaryIndex C D,
        originalIIDAuxiliaryCell C (D.continuous.coefficient i.val) := by
  apply Subset.antisymm
  · intro c hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    exact mem_iUnion.mpr ⟨⟨i, originalIIDAuxiliaryCell_seed_eq_of_mem C _ hi⟩, hi⟩
  · intro c hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    exact mem_iUnion.mpr ⟨i.val, hi⟩

/-- Any cell readout vanishing on the empty set has exactly the same finite
sum over all auxiliary cores and over the true same-seed index subtype. -/
theorem sum_originalIIDAuxiliaryCell_eq_same_seed
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ₀)
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    {A : Type*} [AddCommMonoid A]
    (read : Set (OriginalIIDSeedCoordinateSpace P C.seedIndex) → A)
    (hempty : read ∅ = 0) :
    (∑ i : Fin D.continuous.count, read (originalIIDAuxiliaryCell C (D.continuous.coefficient i))) =
      ∑ i : OriginalIIDSameSeedAuxiliaryIndex C D,
        read (originalIIDAuxiliaryCell C (D.continuous.coefficient i.val)) := by
  classical
  have hzero : (∑ i : {i : Fin D.continuous.count //
      ¬ (D.continuous.coefficient i).seedIndex = C.seedIndex},
      read (originalIIDAuxiliaryCell C (D.continuous.coefficient i.val))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [originalIIDAuxiliaryCell_eq_empty_of_seed_ne C _ i.property, hempty]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin D.continuous.count => (D.continuous.coefficient i).seedIndex = C.seedIndex)
    (fun i => read (originalIIDAuxiliaryCell C (D.continuous.coefficient i)))
  simpa only [hzero, add_zero] using hsplit.symm

end OTSelector.Reconstruction
