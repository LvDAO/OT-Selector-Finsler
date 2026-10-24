import OTSelector.MeasureTheory.PositiveReferenceDensity
import OTSelector.Reconstruction.FinslerSeedRootPartition

/-!
# The original root intensity in the selected seed Haar coordinates

The original common label law on a selected piece is absolutely continuous with
respect to that seed's fixed original reference. Pulling it back to the actual
seed coordinates gives an exact Haar density. Its reciprocal relation with the
fixed conditional-law factor is derived, including finite positive values under
the original population law.
-/

open Set Function MeasureTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original label mass density on one selected piece relative to its fixed
full-seed reference. -/
def populationSeedPieceRootDensity (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ) : Z → ℝ≥0∞ :=
  (lambda.restrict (populationSeedRootPiece P a κ lambda j)).rnDeriv
    (populationSeedLabelReference (P j).seed a (κ j))

/-- The same original intensity in the seed's ambient label space, extended by
zero outside the actual seed labels. -/
def populationSeedPieceHaarDensity (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ) :
    (P j).seed.covector.ker → ℝ≥0∞ :=
  extend ((↑) : (P j).seed.labels → (P j).seed.covector.ker)
    (fun w ↦ populationSeedPieceRootDensity P a κ lambda j (a ((P j).seed.curve w 0)))
    (fun _ ↦ 0)

/-- The original common label measure on one piece, pulled back to the actual seed
label coordinates; its mass is retained without normalization. -/
def populationSeedPieceCoordinateLaw (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ) :
    Measure (P j).seed.covector.ker :=
  ((lambda.restrict (populationSeedRootPiece P a κ lambda j)).comap
    (fun w : (P j).seed.labels ↦ a ((P j).seed.curve w 0))).map
      ((↑) : (P j).seed.labels → (P j).seed.covector.ker)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The ambient Haar density reads the original root density at every actual label. -/
theorem populationSeedPieceHaarDensity_at_label (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → Z) (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (j : ℕ) (w : (P j).seed.labels) :
    populationSeedPieceHaarDensity P a κ lambda j w =
      populationSeedPieceRootDensity P a κ lambda j (a ((P j).seed.curve w 0)) :=
  Subtype.val_injective.extend_apply _ _ w

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSeedIntensityMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The original intensity is globally measurable in the actual seed coordinates. -/
theorem measurable_populationSeedPieceHaarDensity (j : ℕ) :
    Measurable (populationSeedPieceHaarDensity P a κ lambda j) := by
  have he := measurableEmbedding_populationSeedLabel (P j).seed hF hcomplete hu ha hinj
  exact (MeasurableEmbedding.subtype_coe (P j).seed.labels_measurable).measurable_extend
    ((Measure.measurable_rnDeriv _ _).comp he.measurable) measurable_const

/-- The original label measure on a selected piece is absolutely continuous with
respect to the original full-seed Haar reference. -/
theorem populationSeedRootPiece_absolutelyContinuous [SigmaFinite lambda]
    (j : ℕ) [SigmaFinite (κ j)] :
    lambda.restrict (populationSeedRootPiece P a κ lambda j) ≪
      populationSeedLabelReference (P j).seed a (κ j) := by
  have he := measurableEmbedding_populationSeedLabel (P j).seed hF hcomplete hu ha hinj
  have : SigmaFinite (populationSeedLabelReference (P j).seed a (κ j)) :=
    sigmaFinite_labelReferenceOn (κ j) (P j).seed.labels_measurable he
  exact restrict_absolutelyContinuous_of_rnDeriv_ne_zero _ _
    (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)
    (fun z hz ↦ (populationSeedRootPiece_subset P a κ lambda j hz).2.1)

/-- Weighting the actual seed Haar measure pushes forward to precisely the original
common label law on its selected piece. -/
theorem map_populationSeedPieceHaarDensity_subtype [SigmaFinite lambda]
    (j : ℕ) [SigmaFinite (κ j)] :
    (((κ j).comap ((↑) : (P j).seed.labels → (P j).seed.covector.ker)).withDensity
      (fun w ↦ populationSeedPieceHaarDensity P a κ lambda j w)).map
        (fun w : (P j).seed.labels ↦ a ((P j).seed.curve w 0)) =
      lambda.restrict (populationSeedRootPiece P a κ lambda j) := by
  have he := measurableEmbedding_populationSeedLabel (P j).seed hF hcomplete hu ha hinj
  have : SigmaFinite (populationSeedLabelReference (P j).seed a (κ j)) :=
    sigmaFinite_labelReferenceOn (κ j) (P j).seed.labels_measurable he
  simp_rw [populationSeedPieceHaarDensity_at_label]
  unfold populationSeedPieceRootDensity
  rw [map_withDensity_comp_measurable _ he.measurable (Measure.measurable_rnDeriv _ _)]
  change (populationSeedLabelReference (P j).seed a (κ j)).withDensity
      ((lambda.restrict (populationSeedRootPiece P a κ lambda j)).rnDeriv
        (populationSeedLabelReference (P j).seed a (κ j))) = _
  exact Measure.withDensity_rnDeriv_eq _ _
    (populationSeedRootPiece_absolutelyContinuous P a κ lambda hF hcomplete hu ha hinj j)

/-- The pulled-back original piece law is exactly its physical Haar intensity. -/
theorem populationSeedPieceCoordinateLaw_eq_withDensity [SigmaFinite lambda]
    (j : ℕ) [SigmaFinite (κ j)] :
    populationSeedPieceCoordinateLaw P a κ lambda j =
      ((κ j).restrict (P j).seed.labels).withDensity
        (populationSeedPieceHaarDensity P a κ lambda j) := by
  have he := measurableEmbedding_populationSeedLabel (P j).seed hF hcomplete hu ha hinj
  have hmap := map_populationSeedPieceHaarDensity_subtype P a κ lambda
    hF hcomplete hu ha hinj j
  unfold populationSeedPieceCoordinateLaw
  rw [← hmap, he.comap_map, map_withDensity_comp_measurable _ measurable_subtype_coe
    (measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj j),
    map_comap_subtype_coe (P j).seed.labels_measurable]

/-- On original roots the intensity is finite, positive and the reciprocal of the
same fixed Radon--Nikodym factor used in the original conditional density. -/
theorem ae_populationSeedPieceRootDensity_inv [SigmaFinite lambda]
    (j : ℕ) [SigmaFinite (κ j)] :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      0 < populationSeedPieceRootDensity P a κ lambda j z ∧
      populationSeedPieceRootDensity P a κ lambda j z < (∞ : ℝ≥0∞) ∧
      populationSeedPieceRootDensity P a κ lambda j z =
        ((populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z)⁻¹ := by
  have he := measurableEmbedding_populationSeedLabel (P j).seed hF hcomplete hu ha hinj
  have : SigmaFinite (populationSeedLabelReference (P j).seed a (κ j)) :=
    sigmaFinite_labelReferenceOn (κ j) (P j).seed.labels_measurable he
  exact ae_restricted_reference_density_inv _ _
    (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)
    (fun z hz ↦ (populationSeedRootPiece_subset P a κ lambda j hz).2.1)

end OTSelector.Reconstruction
