import OTSelector.Reconstruction.FinslerPopulationSeedIntensity
import OTSelector.Reconstruction.FinslerCoefficientCoreLabel

/-!
# Original population intensity on retained seed cores

Every retained core carries its original mass and the same Haar intensity as its
selected seed piece. No probability normalization is performed.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSeedCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The coordinate intensity at the retained original label is precisely the
original root density. -/
theorem populationSeedPieceHaarDensity_at_root (j : ℕ) {z : Z}
    (hz : z ∈ populationSeedRootPiece P a κ lambda j) :
    populationSeedPieceHaarDensity P a κ lambda j
        (populationSeedRootLabelValue (P j).seed a z) =
      populationSeedPieceRootDensity P a κ lambda j z := by
  rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hz⟩,
    populationSeedPieceHaarDensity_at_label,
    populationSeedPieceLabel_root P a κ lambda j ⟨z, hz⟩]

/-- The original population mass in actual label coordinates has exactly the mass
of the retained roots, without renormalizing either population. -/
theorem populationSeedCoreCoordinateLaw_mass (j : ℕ) (K : Set Z) :
    ((lambda.restrict K).map (populationSeedRootLabelValue (P j).seed a)) univ =
      lambda K := by
  rw [Measure.map_apply (measurable_populationSeedRootLabelValue (P j).seed
    hF hcomplete hu ha hinj) MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]

/-- Retaining original roots in a selected piece retains the same Haar intensity,
restricted to the exact image of these roots in the actual seed labels. -/
theorem map_populationSeedCore_eq_withDensity [SigmaFinite lambda]
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j) :
    (lambda.restrict K).map (populationSeedRootLabelValue (P j).seed a) =
      ((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).withDensity
        (populationSeedPieceHaarDensity P a κ lambda j) := by
  let S := (P j).seed
  let f : S.labels → Z := fun w ↦ a (S.curve w 0)
  let r := populationSeedRootLabelValue S a
  let m := (κ j).comap ((↑) : S.labels → S.covector.ker)
  let d := populationSeedPieceHaarDensity P a κ lambda j
  have he : MeasurableEmbedding f :=
    measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj
  have hv := MeasurableEmbedding.subtype_coe S.labels_measurable
  have hr : Measurable r :=
    measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hd : Measurable d :=
    measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj j
  have hinverse (w : S.labels) : r (f w) = w.val :=
    populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj w
  have himage : r '' K = ((↑) : S.labels → S.covector.ker) '' (f ⁻¹' K) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      let v := populationSeedPieceLabel P a κ lambda j ⟨z, hsub hz⟩
      have hvroot : f v = z := populationSeedPieceLabel_root P a κ lambda j ⟨z, hsub hz⟩
      exact ⟨v, by simpa only [mem_preimage, hvroot] using hz,
        (hinverse v).symm.trans (congrArg r hvroot)⟩
    · rintro ⟨v, hvK, rfl⟩
      exact ⟨f v, hvK, hinverse v⟩
  have himageSub : r '' K ⊆ S.labels := by
    rw [himage]
    rintro _ ⟨w, _, rfl⟩
    exact w.property
  have hmap : (m.withDensity (fun w ↦ d w)).map f =
      lambda.restrict (populationSeedRootPiece P a κ lambda j) :=
    map_populationSeedPieceHaarDensity_subtype P a κ lambda hF hcomplete hu ha hinj j
  change (lambda.restrict K).map r = ((κ j).restrict (r '' K)).withDensity d
  calc
    (lambda.restrict K).map r =
        (((m.withDensity (fun w ↦ d w)).map f).restrict K).map r := by
      rw [hmap, Measure.restrict_restrict_of_subset hsub]
    _ = (((m.withDensity (fun w ↦ d w)).restrict (f ⁻¹' K)).map
        ((↑) : S.labels → S.covector.ker)) := by
      rw [he.restrict_map, Measure.map_map hr he.measurable]
      congr 1
      exact funext hinverse
    _ = ((m.restrict (f ⁻¹' K)).map ((↑) : S.labels → S.covector.ker)).withDensity d := by
      rw [restrict_withDensity (he.measurable hK),
        map_withDensity_comp_measurable _ measurable_subtype_coe hd]
    _ = ((m.map ((↑) : S.labels → S.covector.ker)).restrict (r '' K)).withDensity d := by
      rw [hv.restrict_map, himage, hv.injective.preimage_image]
    _ = ((κ j).restrict (r '' K)).withDensity d := by
      rw [map_comap_subtype_coe S.labels_measurable,
        Measure.restrict_restrict_of_subset himageSub]

end OTSelector.Reconstruction
