import OTSelector.Probability.FinslerAtlasCoordinateFacts
import OTSelector.Reconstruction.FinslerPopulationSeedIntensity
import OTSelector.MeasureTheory.ConditionalWindowConsistency

/-!
# The two cube-law inputs: Haar pushforward and constant seed density

`OTSelector.Probability.FinslerAtlasCoordinateFacts` reduced the normalized
seed-coordinate cube law to two inputs on the retained label core
`A = populationSeedRootLabelValue (P j).seed a '' K`:

* `hconst`: the piece Haar density `populationSeedPieceHaarDensity P a κ lambda j`
  is almost everywhere constant `c ≠ 0, ∞` on `A`;
* `hhaar`: `(κ j A)⁻¹ • ((κ j).restrict A).map e = cubeMeasure (Fin q) 1`.

This module analyses both inputs and proves the strongest available
reductions.

## `hhaar` from the normalized Haar pushforward and a cube image

`hhaar_of_map_eq_smul_volume` proves `hhaar` from exactly two geometric
hypotheses:

* `hmap : (κ j).map e = c • volume` — the Haar measure pushed through the
  basis coordinate `e` is a scalar multiple of Lebesgue measure;
* `himage : e '' A = seedUnitCube q` — the retained label set is a coordinate
  cube in the `e`-coordinates, where `seedUnitCube q = univ.pi (fun _ => Ioo 0 1)`.

The proof uses `MeasurableEmbedding.restrict_map` to move the restriction through
`e`, `Measure.restrict_pi_pi` to identify the normalized volume restriction on the
unit cube with `cubeMeasure`, and cancels the scalar using the mass identity
`κ j A = c`.  `cubeMeasure_eq_volume_restrict_seedUnitCube` records the cube
identification separately.

`map_eq_smul_volume_of_isAddHaarMeasure` then *discharges* `hmap` from the atlas
Haar instance `hκ : ∀ j, (κ j).IsAddHaarMeasure`: pushing a Haar measure through
the continuous linear equivalence `e` gives a Haar measure on `Fin q → ℝ`, and
`isAddLeftInvariant_eq_smul` identifies it with
`addHaarScalarFactor ((κ j).map e) volume • volume`.  The scalar factor is
positive and finite by `addHaarScalarFactor_pos_of_isAddHaarMeasure`, and
`isAddHaarMeasure_volume_pi` supplies the Haar instance for Lebesgue measure.
Consequently `hhaar_of_isAddHaarMeasure_and_image_cube` needs only the Haar
instance and the cube image.

The only residual geometric input is therefore `himage`:
`populationSeedRootPiece` is defined by the nonvanishing of the reference
Radon--Nikodym factor (`populationSeedReferenceRoots`), not by a coordinate cube,
and no atlas field records that the retained roots form a unit cube in the
`e`-coordinates.

## `hconst` from the ratio form of the density

`populationSeedPieceHaarDensity` is *not* literally constant: by
`populationSeedPieceHaarDensity_at_label` it extends
`populationSeedPieceRootDensity`, the Radon--Nikodym derivative
`d(lambda.restrict rootPiece)/d(populationSeedLabelReference)` evaluated at the
root label.  `populationSeedPieceRootDensity_const_of_label_law_smul` proves that
it is a.e. `c` when the population label piece law is proportional to the seed
label reference:

`hprop : lambda.restrict (populationSeedRootPiece P a κ lambda j) = c • populationSeedLabelReference (P j).seed a (κ j)`.

The proof is `Measure.rnDeriv_smul_left_of_ne_top'` together with
`Measure.rnDeriv_self`.  `populationSeedPieceHaarDensity_const_ae_of_rootDensity_const`
transfers the a.e. constancy from the label reference to the Haar restriction on
the retained label image, using the measurable embedding
`f w = a (S.curve w 0)` and the identity
`r '' K = (↑) '' (f ⁻¹' K)` (proved from `K ⊆ populationSeedRootPiece`, exactly
as in `map_populationSeedCore_eq_withDensity`).

## Combined theorem

`normalized_seed_coordinate_law_of_atlas` combines the two reductions with
`normalized_seed_coordinate_law_eq_cubeMeasure`, so the cube law follows from the
atlas fields plus `hprop`, `hmap` and `himage`.
`normalized_seed_coordinate_law_of_atlas_haar` removes `hmap` completely: it
assumes only the atlas Haar instance and leaves `hprop` and `himage` as the
residual hypotheses.  These are precisely the uniformity of the population label
density relative to the seed Haar reference and the identification of the
retained seed labels with a unit cube in the `e`-coordinates.

## Gap map

* `hhaar`: the scalar-multiple-of-Lebesgue input `hmap` is now *proved* from the
  atlas Haar instance by `map_eq_smul_volume_of_isAddHaarMeasure`.  The only
  residual input is `himage` (the retained labels form the unit cube).  The atlas
  normalization `S.normalization` and the basis `e` supply the linear coordinate
  identification; a cube partition of the retained roots would supply `himage`.
  Boundary choices (`Ioo` versus `Icc`) are immaterial a.e. and could be absorbed
  by `Measure.restrict_congr_set`.
* `hconst`: supplied by `hprop`, the proportionality of the population label
  piece law to the seed label reference.  In the paper this is the statement that
  the population intensity is uniform on the selected piece relative to the seed
  Haar reference; it is not a consequence of absolute continuity alone.
-/

open MeasureTheory ProbabilityTheory Set Function Manifold OTSelector.Geometry
open MeasureTheory.Measure
open OTSelector.Reconstruction
open scoped BigOperators NNReal ENNReal Topology ContDiff

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The unit cube and `cubeMeasure` as a normalized volume restriction -/

/-- The unit cube in the `Fin q → ℝ` coordinates, matching `uniformInterval 1`. -/
def seedUnitCube (q : ℕ) : Set (Fin q → ℝ) :=
  Set.univ.pi fun _ => Set.Ioo (0 : ℝ) 1

/-- The unit cube is measurable. -/
theorem measurableSet_seedUnitCube (q : ℕ) : MeasurableSet (seedUnitCube q) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- The unit cube has volume one. -/
theorem volume_seedUnitCube (q : ℕ) :
    (volume : Measure (Fin q → ℝ)) (seedUnitCube q) = 1 := by
  rw [seedUnitCube, volume_pi_pi]
  simp [Real.volume_Ioo]

/-- The uniform cube law is the normalized Lebesgue measure restricted to the
unit cube. -/
theorem cubeMeasure_eq_volume_restrict_seedUnitCube (q : ℕ) :
    cubeMeasure (Fin q) 1 = (volume : Measure (Fin q → ℝ)).restrict (seedUnitCube q) := by
  rw [seedUnitCube, cubeMeasure, volume_pi, Measure.restrict_pi_pi]
  simp [uniformInterval, Real.volume_Ioo]

/-! ## `hhaar` from the Haar pushforward and a cube image -/

section HaarCube

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker)

/-- **The Haar cube input.**  If the Haar measure of the seed label space pushes
through the basis coordinate `e` to a scalar multiple of Lebesgue measure, and the
retained label image is exactly the unit cube in these coordinates, then the
normalized restricted Haar pushforward is `cubeMeasure (Fin q) 1`. -/
theorem hhaar_of_map_eq_smul_volume {q : ℕ} (j : ℕ)
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    {K : Set Z} {c : ℝ≥0∞}
    (hmap : (κ j).map e = c • (volume : Measure (Fin q → ℝ)))
    (himage : e '' (populationSeedRootLabelValue (P j).seed a '' K) = seedUnitCube q)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    (κ j (populationSeedRootLabelValue (P j).seed a '' K))⁻¹ •
        (((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).map e) =
      cubeMeasure (Fin q) 1 := by
  let A := populationSeedRootLabelValue (P j).seed a '' K
  change (κ j A)⁻¹ • (((κ j).restrict A).map e) = cubeMeasure (Fin q) 1
  have himageA : e '' A = seedUnitCube q := himage
  have hUmeas : MeasurableSet (seedUnitCube q) := measurableSet_seedUnitCube q
  have heA : MeasurableSet (e '' A) := himageA.symm ▸ hUmeas
  have hAmeas : MeasurableSet A := by
    have hAeq : A = e ⁻¹' seedUnitCube q := by
      rw [← himageA]
      exact (e.injective.preimage_image A).symm
    rw [hAeq]
    exact hUmeas.preimage e.continuous.measurable
  have hrestrict : ((κ j).restrict A).map e = ((κ j).map e).restrict (e '' A) := by
    rw [Measure.restrict_map e.continuous.measurable heA, e.injective.preimage_image]
  have hcube : (volume : Measure (Fin q → ℝ)).restrict (seedUnitCube q) =
      cubeMeasure (Fin q) 1 :=
    (cubeMeasure_eq_volume_restrict_seedUnitCube q).symm
  have hmaprestrict : ((κ j).restrict A).map e = c • cubeMeasure (Fin q) 1 := by
    rw [hrestrict, hmap, himageA, Measure.restrict_smul, hcube]
  have hmass : κ j A = c := by
    have hmapA : (κ j).map e (e '' A) = κ j A := by
      rw [Measure.map_apply e.continuous.measurable heA]
      exact congrArg (κ j) (e.injective.preimage_image A)
    calc
      κ j A = (κ j).map e (e '' A) := hmapA.symm
      _ = (c • (volume : Measure (Fin q → ℝ))) (seedUnitCube q) := by rw [hmap, himageA]
      _ = c * (volume : Measure (Fin q → ℝ)) (seedUnitCube q) := by
            rw [Measure.smul_apply, smul_eq_mul]
      _ = c * 1 := by rw [volume_seedUnitCube]
      _ = c := mul_one c
  calc
    (κ j A)⁻¹ • ((κ j).restrict A).map e
        = (κ j A)⁻¹ • (c • cubeMeasure (Fin q) 1) := by rw [hmaprestrict]
    _ = ((κ j A)⁻¹ * c) • cubeMeasure (Fin q) 1 := by rw [smul_smul]
    _ = cubeMeasure (Fin q) 1 := by
          rw [hmass, ENNReal.inv_mul_cancel hc0 hctop, one_smul]

/-- **A Haar measure pushed through a linear equivalence is a scalar multiple of
Lebesgue measure.**  This discharges the `hmap` input of
`hhaar_of_map_eq_smul_volume` from the atlas Haar instance
`hκ : ∀ j, (κ j).IsAddHaarMeasure`; the scalar is `addHaarScalarFactor`, which is
positive and finite because both measures are Haar measures. -/
theorem map_eq_smul_volume_of_isAddHaarMeasure {q : ℕ} (j : ℕ)
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    [IsAddHaarMeasure (κ j)] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (κ j).map e = c • (volume : Measure (Fin q → ℝ)) := by
  haveI : IsAddHaarMeasure ((κ j).map e) := e.isAddHaarMeasure_map (κ j)
  haveI : IsAddHaarMeasure (volume : Measure (Fin q → ℝ)) :=
    isAddHaarMeasure_volume_pi (Fin q)
  refine ⟨(addHaarScalarFactor ((κ j).map e) (volume : Measure (Fin q → ℝ)) : ℝ≥0∞),
    ?_, ?_, ?_⟩
  · rw [ENNReal.coe_ne_zero]
    exact ne_of_gt (addHaarScalarFactor_pos_of_isAddHaarMeasure _ _)
  · exact ENNReal.coe_ne_top
  · simpa only [Measure.coe_nnreal_smul] using
      isAddLeftInvariant_eq_smul ((κ j).map e) (volume : Measure (Fin q → ℝ))

/-- **The Haar cube input from the atlas Haar instance and a cube image.** -/
theorem hhaar_of_isAddHaarMeasure_and_image_cube {q : ℕ} (j : ℕ)
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    [IsAddHaarMeasure (κ j)] {K : Set Z}
    (himage : e '' (populationSeedRootLabelValue (P j).seed a '' K) = seedUnitCube q) :
    (κ j (populationSeedRootLabelValue (P j).seed a '' K))⁻¹ •
        (((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).map e) =
      cubeMeasure (Fin q) 1 := by
  obtain ⟨c, hc0, hctop, hmap⟩ :=
    map_eq_smul_volume_of_isAddHaarMeasure (P := P) (κ := κ) (j := j) (e := e)
  exact hhaar_of_map_eq_smul_volume P a κ j e hmap himage hc0 hctop

end HaarCube

/-! ## `hconst`: the ratio form and its uniformity hypothesis -/

section DensityConst

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instCubeInputsMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **The density ratio is constant if the piece law is proportional to the seed
reference.**  If the population label law restricted to the selected root piece
is `c` times the seed label reference, then the Radon--Nikodym density
`populationSeedPieceRootDensity` is a.e. `c` for the seed label reference. -/
theorem populationSeedPieceRootDensity_const_of_label_law_smul (j : ℕ)
    [SigmaFinite lambda] [SigmaFinite (κ j)]
    {c : ℝ≥0∞} (hctop : c ≠ ⊤)
    (hprop : lambda.restrict (populationSeedRootPiece P a κ lambda j) =
      c • populationSeedLabelReference (P j).seed a (κ j)) :
    populationSeedPieceRootDensity P a κ lambda j =ᵐ[
      populationSeedLabelReference (P j).seed a (κ j)] (fun _ => c) := by
  haveI hσ : SigmaFinite (populationSeedLabelReference (P j).seed a (κ j)) :=
    sigmaFinite_labelReferenceOn (κ j) (P j).seed.labels_measurable
      (measurableEmbedding_populationSeedLabel (P j).seed hF hcomplete hu ha hinj)
  unfold populationSeedPieceRootDensity
  rw [hprop]
  have hsmul : (c • populationSeedLabelReference (P j).seed a (κ j)).rnDeriv
      (populationSeedLabelReference (P j).seed a (κ j)) =ᵐ[
        populationSeedLabelReference (P j).seed a (κ j)]
      c • (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv
        (populationSeedLabelReference (P j).seed a (κ j)) :=
    Measure.rnDeriv_smul_left_of_ne_top' _ _ hctop
  filter_upwards [hsmul,
    Measure.rnDeriv_self (populationSeedLabelReference (P j).seed a (κ j))] with z hz hself
  rw [hz]
  simp only [Pi.smul_apply, hself, smul_eq_mul, mul_one]

/-- **Transfer of the a.e. density constancy to the Haar restriction on the
retained label image.**  This is the bridge from the ratio form
`populationSeedPieceRootDensity` to the exact `hconst` shape used in
`normalized_seed_coordinate_law_eq_cubeMeasure`. -/
theorem populationSeedPieceHaarDensity_const_ae_of_rootDensity_const (j : ℕ)
    [SigmaFinite (κ j)] {c : ℝ≥0∞} {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    (hroot : populationSeedPieceRootDensity P a κ lambda j =ᵐ[
      populationSeedLabelReference (P j).seed a (κ j)] (fun _ => c)) :
    populationSeedPieceHaarDensity P a κ lambda j =ᵐ[(κ j).restrict
      (populationSeedRootLabelValue (P j).seed a '' K)] (fun _ => c) := by
  let S := (P j).seed
  let f : S.labels → Z := fun w => a (S.curve w 0)
  let r : Z → S.covector.ker := populationSeedRootLabelValue S a
  have hf : MeasurableEmbedding f :=
    measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj
  have hinverse (w : S.labels) : r (f w) = ((↑) : S.labels → S.covector.ker) w :=
    populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj w
  have himage : r '' K = ((↑) : S.labels → S.covector.ker) '' (f ⁻¹' K) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      let w' := populationSeedPieceLabel P a κ lambda j ⟨z, hsub hz⟩
      have hw' : f w' = z := populationSeedPieceLabel_root P a κ lambda j ⟨z, hsub hz⟩
      exact ⟨w', by simpa only [mem_preimage, hw'] using hz,
        (hinverse w').symm.trans (congrArg r hw')⟩
    · rintro ⟨w', hw', rfl⟩
      exact ⟨f w', hw', hinverse w'⟩
  have hAsub : r '' K ⊆ S.labels := by
    rw [himage]
    rintro _ ⟨w, _, rfl⟩
    exact w.property
  have hpre : ((↑) : S.labels → S.covector.ker) ⁻¹' (r '' K) = f ⁻¹' K := by
    rw [himage]
    exact (MeasurableEmbedding.subtype_coe S.labels_measurable).injective.preimage_image _
  have hAmeas : MeasurableSet (r '' K) := by
    rw [himage]
    exact (MeasurableEmbedding.subtype_coe S.labels_measurable).measurableSet_image.mpr
      (hK.preimage hf.measurable)
  have hmeasure : (κ j).restrict (r '' K) =
      (((κ j).comap ((↑) : S.labels → S.covector.ker)).restrict (f ⁻¹' K)).map
        ((↑) : S.labels → S.covector.ker) := by
    rw [← hpre]
    rw [← Measure.restrict_map (μ := (κ j).comap ((↑) : S.labels → S.covector.ker))
      (f := ((↑) : S.labels → S.covector.ker)) measurable_subtype_coe hAmeas]
    rw [map_comap_subtype_coe S.labels_measurable]
    exact (Measure.restrict_restrict_of_subset hAsub).symm
  have hroot' : populationSeedPieceRootDensity P a κ lambda j =ᵐ[
      ((κ j).comap ((↑) : S.labels → S.covector.ker)).map f] (fun _ => c) := by
    simpa only [populationSeedLabelReference, labelReferenceOn, S, f] using hroot
  have hae_sub : ∀ᵐ w ∂(((κ j).comap ((↑) : S.labels → S.covector.ker)).restrict
      (f ⁻¹' K)), populationSeedPieceRootDensity P a κ lambda j (f w) = c := by
    have h1 : ∀ᵐ z ∂(((κ j).comap ((↑) : S.labels → S.covector.ker)).map f).restrict
        (f '' (f ⁻¹' K)), populationSeedPieceRootDensity P a κ lambda j z = c :=
      ae_restrict_of_ae hroot'
    rw [hf.restrict_map ((κ j).comap ((↑) : S.labels → S.covector.ker))
      (f '' (f ⁻¹' K))] at h1
    have h2 : ∀ᵐ w ∂(((κ j).comap ((↑) : S.labels → S.covector.ker)).restrict
        (f ⁻¹' (f '' (f ⁻¹' K)))), populationSeedPieceRootDensity P a κ lambda j (f w) = c :=
      hf.ae_map_iff.mp h1
    rwa [hf.injective.preimage_image] at h2
  have hae : ∀ᵐ (w : S.labels) ∂(((κ j).comap
      ((↑) : S.labels → S.covector.ker)).restrict (f ⁻¹' K)),
      populationSeedPieceHaarDensity P a κ lambda j w = c := by
    filter_upwards [hae_sub] with w hw
    rw [populationSeedPieceHaarDensity_at_label P a κ lambda j w]
    exact hw
  rw [hmeasure]
  exact (MeasurableEmbedding.subtype_coe S.labels_measurable).ae_map_iff.mpr hae

/-- **The density input `hconst` from a uniform population density.**  Combining
the ratio form with the proportionality hypothesis yields exactly the `hconst`
hypothesis of the cube-law theorem. -/
theorem populationSeedPieceHaarDensity_const_of_label_law_smul (j : ℕ)
    [SigmaFinite lambda] [SigmaFinite (κ j)]
    {c : ℝ≥0∞} (hctop : c ≠ ⊤)
    (hprop : lambda.restrict (populationSeedRootPiece P a κ lambda j) =
      c • populationSeedLabelReference (P j).seed a (κ j))
    {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j) :
    populationSeedPieceHaarDensity P a κ lambda j =ᵐ[(κ j).restrict
      (populationSeedRootLabelValue (P j).seed a '' K)] (fun _ => c) :=
  populationSeedPieceHaarDensity_const_ae_of_rootDensity_const P a κ lambda
    hF hcomplete hu ha hinj j hK hsub
    (populationSeedPieceRootDensity_const_of_label_law_smul P a κ lambda
      hF hcomplete hu ha hinj j hctop hprop)

/-- **Cube law from the atlas fields and the two residual inputs.**  The
normalized seed-coordinate law on the retained core is the uniform cube law,
assuming the uniform population density `hprop`, the Haar pushforward `hmap` and
the cube identification `himage`. -/
theorem normalized_seed_coordinate_law_of_atlas {q : ℕ} (j : ℕ)
    [SigmaFinite lambda] [SigmaFinite (κ j)]
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    {c c' : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hprop : lambda.restrict (populationSeedRootPiece P a κ lambda j) =
      c • populationSeedLabelReference (P j).seed a (κ j))
    (hmap : (κ j).map e = c' • (volume : Measure (Fin q → ℝ)))
    (hc'0 : c' ≠ 0) (hc'top : c' ≠ ⊤)
    (himage : e '' (populationSeedRootLabelValue (P j).seed a '' K) = seedUnitCube q) :
    (lambda K)⁻¹ • (lambda.restrict K).map
        (atlasSeedCoord (P j).seed e a) = cubeMeasure (Fin q) 1 := by
  refine normalized_seed_coordinate_law_eq_cubeMeasure P a κ lambda
    hF hcomplete hu ha hinj j e hK hsub ?_ hc0 hctop ?_
  · exact populationSeedPieceHaarDensity_const_of_label_law_smul P a κ lambda
      hF hcomplete hu ha hinj j hctop hprop hK hsub
  · exact hhaar_of_map_eq_smul_volume P a κ j e hmap himage hc'0 hc'top

/-- **Cube law from the atlas fields, the Haar instance and the cube image.**  The
Haar pushforward scalar is produced internally by
`map_eq_smul_volume_of_isAddHaarMeasure`, so the only residual inputs are the
uniform population density `hprop` and the cube identification `himage`. -/
theorem normalized_seed_coordinate_law_of_atlas_haar {q : ℕ} (j : ℕ)
    [SigmaFinite lambda] [SigmaFinite (κ j)] [IsAddHaarMeasure (κ j)]
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hprop : lambda.restrict (populationSeedRootPiece P a κ lambda j) =
      c • populationSeedLabelReference (P j).seed a (κ j))
    (himage : e '' (populationSeedRootLabelValue (P j).seed a '' K) = seedUnitCube q) :
    (lambda K)⁻¹ • (lambda.restrict K).map
        (atlasSeedCoord (P j).seed e a) = cubeMeasure (Fin q) 1 := by
  refine normalized_seed_coordinate_law_eq_cubeMeasure P a κ lambda
    hF hcomplete hu ha hinj j e hK hsub ?_ hc0 hctop ?_
  · exact populationSeedPieceHaarDensity_const_of_label_law_smul P a κ lambda
      hF hcomplete hu ha hinj j hctop hprop hK hsub
  · exact hhaar_of_isAddHaarMeasure_and_image_cube
      (P := P) (a := a) (κ := κ) (j := j) (e := e) himage

end DensityConst

end OTSelector.Probability
