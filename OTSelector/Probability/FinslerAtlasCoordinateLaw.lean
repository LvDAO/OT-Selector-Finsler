import OTSelector.Probability.FinslerMarkedAtlasIdentification
import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import OTSelector.Reconstruction.FinslerPopulationSeedIntensityCore

/-!
# Concrete atlas coordinate and mark maps, and their law reduction

This module instantiates the abstract M2 reduction of
`OTSelector.Probability.FinslerMarkedAtlasIdentification` with the concrete
atlas fields of `OTSelector.Reconstruction`.

## Definitions

* `seedBasisCoord S e w = e w`: the normalized linear-basis coordinate of a seed
  label `w : S.covector.ker`, where `e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)` is a
  continuous linear basis coordinate (in the atlas, built from
  `Module.finBasis ℝ S.covector.ker` and the seed normalization
  `S.normalization : (ℝ × S.covector.ker) ≃L[ℝ] E`).
* `atlasSeedCoord S e a z = e (populationSeedRootLabelValue S a z)`: the atlas
  cube coordinate of a common label `z : Z`.  The inverse label
  `populationSeedRootLabelValue S a` (`FinslerCoefficientCoreLabel`) recovers the
  seed label whose root `S.curve w 0` carries the label `z`.
* `atlasSeedMark mark z = mark z`: the remaining (`A`-component) label
  coordinate, supplied by a measurable map `mark : Z → A`.
* `atlasSeedMarkMap S e a mark z = (atlasSeedCoord S e a z, atlasSeedMark mark z)`.

`atlasSeedCoord_at_root` records the defining relation with the atlas: at an
original root, `atlasSeedCoord S e a (a (S.curve w 0)) = e w`.  The coordinate is
therefore exactly the normalized seed label of the root.

## Law reduction

`map_normalized_label_atlasSeedMarkMap_eq_markedOnePointLaw` is the M2
pushforward identity for the normalized label law of a tile:
`((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map (atlasSeedMarkMap S e a mark) =
  markedOnePointLaw q A α`,
under the three reductions
(i) the normalized atlas cube-coordinate law is `cubeMeasure (Fin q) 1`,
(ii) the mark marginal law is `α`,
(iii) the coordinate and the mark are independent.

`map_restrict_preimage_eq` and `map_normalized_restrict_comp_eq` transfer the
identity from the label law `lam` to the physical law `η` using the atlas field
`label_law : η.map a = lambda` of `PopulationConditionalWindowLaw`;
`physical_normalized_tile_mark_eq_markedOnePointLaw` is the resulting physical
statement; `physical_normalized_target_tile_atlasSeedMarkMap_eq_markedOnePointLaw`
is the target analogue with the target mark space `B`.

## Gap map

The three reductions are not yet derived from the reconstruction fields; this
module isolates them precisely for the concrete atlas maps.

* (i) Atlas supply: `map_populationSeedCore_eq_withDensity` and
  `populationSeedPieceCoordinateLaw_eq_withDensity` identify the coordinate law
  of a piece as the seed Haar measure `κ j` restricted to the retained labels,
  weighted by `populationSeedPieceHaarDensity`.  To obtain `cubeMeasure` one needs
  (a) the seed Haar measure `κ j` (`IsAddHaarMeasure`, available in
  `populationConditionalWindowLaw_of_atlas`) pushed through `e` and normalized to
  the unit cube to be the uniform cube law, and (b) the Haar density to be the
  constant uniform density on the cube (the uniform reference of
  `populationSeedLabelReference`).  The normalization `S.normalization` and the
  basis `e` supply the coordinate identification; the constancy of the density is
  the missing analytic input.
* (ii) Atlas supply: `PopulationConditionalWindowLaw.label_law` identifies `lam`
  with the physical label law `η.map a`; the tile law is `lam.restrict
  (labZ ⁻¹' {c})`.  The missing input is the identification of the normalized
  mark marginal with the marked population law `α` (in the intended application
  `mark` is the coefficient-core mark and `α` its local law).
* (iii) Atlas supply: the product factorization in
  `PopulationConditionalWindowLaw` (`window_law`, `joint_law`,
  `conditional_law`): the joint density splits into the label-coordinate factor
  (`populationWindowLabelReference`) and the population factor.  The missing input
  is that the mark conditional law does not depend on the seed coordinate, i.e.
  the factorization is a product with the coordinate factor.
-/

open MeasureTheory ProbabilityTheory Set Function Manifold OTSelector.Geometry
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

section Definitions

/-- The normalized linear-basis coordinate of a seed label. -/
noncomputable def seedBasisCoord {q : ℕ} (S : F.CalibratedLevelSeedPatch u)
    (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)) (w : S.covector.ker) : Fin q → ℝ :=
  e w

/-- **Atlas cube coordinate.**  The seed label of a common label `z : Z`, read in
the normalized linear-basis coordinates `e`.  The inverse label
`populationSeedRootLabelValue S a z` recovers the seed label whose root carries
the label `z`. -/
noncomputable def atlasSeedCoord {q : ℕ} (S : F.CalibratedLevelSeedPatch u)
    (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)) (a : M → Z) (z : Z) : Fin q → ℝ :=
  e (populationSeedRootLabelValue S a z)

/-- **Atlas mark.**  The remaining (`A`-component) label coordinate. -/
def atlasSeedMark {A : Type*} (mark : Z → A) (z : Z) : A :=
  mark z

/-- Measurability of the atlas mark. -/
theorem measurable_atlasSeedMark {A : Type*} [MeasurableSpace A] (mark : Z → A)
    (hm : Measurable mark) : Measurable (atlasSeedMark mark) :=
  hm

/-- The atlas mark map: the cube coordinate together with the mark. -/
def atlasSeedMarkMap {q : ℕ} {A : Type*} (S : F.CalibratedLevelSeedPatch u)
    (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)) (a : M → Z) (mark : Z → A) :
    Z → (Fin q → ℝ) × A :=
  fun z => (atlasSeedCoord S e a z, atlasSeedMark mark z)

end Definitions

section Measurability

variable (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instAtlasCoordMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  {a : M → Z} (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include S hF hcomplete hu ha hinj

/-- At an original root, the atlas cube coordinate is the normalized seed label. -/
theorem atlasSeedCoord_at_root {q : ℕ} (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (w : S.labels) :
    atlasSeedCoord S e a (a (S.curve w 0)) = e w := by
  unfold atlasSeedCoord
  rw [populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj w]

/-- Measurability of the atlas cube coordinate. -/
theorem measurable_atlasSeedCoord {q : ℕ} (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)) :
    Measurable (atlasSeedCoord S e a) :=
  e.continuous.measurable.comp
    (measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj)

/-- Measurability of the atlas mark map. -/
theorem measurable_atlasSeedMarkMap {q : ℕ} {A : Type*} [MeasurableSpace A]
    (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ)) (mark : Z → A) (hm : Measurable mark) :
    Measurable (atlasSeedMarkMap S e a mark) :=
  (measurable_atlasSeedCoord S hF hcomplete hu ha hinj e).prodMk
    (measurable_atlasSeedMark mark hm)

end Measurability


section LabelLaw

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- **Atlas pushforward identity for the normalized label law of a tile.**  Under
the three atlas reductions (uniform cube-coordinate law, mark marginal `α`,
independence), the atlas mark map pushes the normalized label law of a tile
forward to the marked one-point law. -/
theorem map_normalized_label_atlasSeedMarkMap_eq_markedOnePointLaw {q : ℕ}
    (S : F.CalibratedLevelSeedPatch u) (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (a : M → Z) {A : Type*} [MeasurableSpace A] (mark : Z → A) (α : Measure A)
    (labZ : Z → ι) (c : ι) (lam : Measure Z) [IsProbabilityMeasure lam]
    (hρ : lam (labZ ⁻¹' {c}) ≠ 0)
    (hcoord : Measurable (atlasSeedCoord S e a)) (hmark : Measurable mark)
    (hcube : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedCoord S e a) = cubeMeasure (Fin q) 1)
    (hmarkLaw : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedMark mark) = α)
    (hindep : IndepFun (atlasSeedCoord S e a) (atlasSeedMark mark)
      ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c}))) :
    ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedMarkMap S e a mark) = markedOnePointLaw q A α :=
  map_normalized_tile_atlasMarkMap_eq_markedOnePointLaw lam labZ c hρ
    (atlasSeedCoord S e a) (atlasSeedMark mark) hcoord hmark hcube hmarkLaw hindep

end LabelLaw

section PhysicalTransfer

/-- The label pushforward of a restricted physical measure. -/
theorem map_restrict_preimage_eq (η : Measure M) (a : M → Z) (lam : Measure Z)
    (ha : Measurable a) (hlaw : η.map a = lam) {K : Set Z} (hK : MeasurableSet K) :
    (η.restrict (a ⁻¹' K)).map a = lam.restrict K := by
  ext B hB
  calc (η.restrict (a ⁻¹' K)).map a B
      = (η.restrict (a ⁻¹' K)) (a ⁻¹' B) := Measure.map_apply ha hB
    _ = η ((a ⁻¹' B) ∩ (a ⁻¹' K)) := Measure.restrict_apply (ha hB)
    _ = η (a ⁻¹' (B ∩ K)) := by rw [Set.preimage_inter]
    _ = η (a ⁻¹' (K ∩ B)) := by rw [Set.inter_comm B K]
    _ = (η.map a) (K ∩ B) := (Measure.map_apply ha (hK.inter hB)).symm
    _ = lam (K ∩ B) := by rw [hlaw]
    _ = (lam.restrict K) B := by rw [Set.inter_comm K B, ← Measure.restrict_apply hB]

/-- The normalized physical tile law pushes forward under the common label map
to the normalized label tile law. -/
theorem map_normalized_restrict_preimage_eq (η : Measure M) (a : M → Z) (lam : Measure Z)
    (ha : Measurable a) (hlaw : η.map a = lam) {K : Set Z} (hK : MeasurableSet K) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map a = (lam K)⁻¹ • lam.restrict K := by
  have hmass : η (a ⁻¹' K) = lam K := by
    rw [← hlaw, Measure.map_apply ha hK]
  rw [hmass, Measure.map_smul, map_restrict_preimage_eq η a lam ha hlaw hK]

/-- The normalized physical tile pushforward under a mark map that factors
through the common label. -/
theorem map_normalized_restrict_comp_eq (η : Measure M) (a : M → Z) (lam : Measure Z)
    (ha : Measurable a) (hlaw : η.map a = lam) {K : Set Z} (hK : MeasurableSet K)
    {X : Type*} [MeasurableSpace X] (markMap : Z → X)
    (hmarkMap : Measurable markMap) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map (fun x => markMap (a x)) =
      ((lam K)⁻¹ • lam.restrict K).map markMap := by
  change Measure.map (markMap ∘ a) ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)) =
    Measure.map markMap ((lam K)⁻¹ • lam.restrict K)
  rw [← Measure.map_map hmarkMap ha]
  exact congrArg (fun ν => ν.map markMap)
    (map_normalized_restrict_preimage_eq η a lam ha hlaw hK)

/-- **Physical atlas identification.**  If the normalized label tile law pushes
forward under a mark map to the marked one-point law, then the normalized
physical tile law does as well, for the mark map `x ↦ markMap (a x)`. -/
theorem physical_normalized_tile_mark_eq_markedOnePointLaw
    (η : Measure M) [IsProbabilityMeasure η] (a : M → Z) (lam : Measure Z)
    [IsProbabilityMeasure lam] (ha : Measurable a) (hlaw : η.map a = lam)
    {K : Set Z} (hK : MeasurableSet K)
    {q : ℕ} {A : Type*} [MeasurableSpace A] (markMap : Z → (Fin q → ℝ) × A)
    (α : Measure A) (hmarkMap : Measurable markMap)
    (hlabel : ((lam K)⁻¹ • lam.restrict K).map markMap = markedOnePointLaw q A α) :
    ((η (a ⁻¹' K))⁻¹ • η.restrict (a ⁻¹' K)).map (fun x => markMap (a x)) =
      markedOnePointLaw q A α := by
  rw [map_normalized_restrict_comp_eq η a lam ha hlaw hK markMap hmarkMap]
  exact hlabel

end PhysicalTransfer

section PhysicalAtlas

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- **Physical atlas identification for the concrete atlas mark map.**  The
normalized physical tile law of `labZ ∘ a` pushes forward under
`x ↦ atlasSeedMarkMap S e a mark (a x)` to the marked one-point law, under the
three atlas reductions on the normalized label law. -/
theorem physical_normalized_tile_atlasSeedMarkMap_eq_markedOnePointLaw {q : ℕ}
    (S : F.CalibratedLevelSeedPatch u) (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (a : M → Z) {A : Type*} [MeasurableSpace A] (mark : Z → A) (α : Measure A)
    (labZ : Z → ι) (hlabZ : Measurable labZ) (c : ι)
    (η : Measure M) [IsProbabilityMeasure η] (lam : Measure Z) [IsProbabilityMeasure lam]
    (ha : Measurable a) (hlaw : η.map a = lam)
    (hρ : lam (labZ ⁻¹' {c}) ≠ 0)
    (hmarkMap : Measurable (atlasSeedMarkMap S e a mark))
    (hcoord : Measurable (atlasSeedCoord S e a)) (hmark : Measurable mark)
    (hcube : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedCoord S e a) = cubeMeasure (Fin q) 1)
    (hmarkLaw : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedMark mark) = α)
    (hindep : IndepFun (atlasSeedCoord S e a) (atlasSeedMark mark)
      ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c}))) :
    ((η (a ⁻¹' (labZ ⁻¹' {c})))⁻¹ • η.restrict (a ⁻¹' (labZ ⁻¹' {c}))).map
        (fun x => atlasSeedMarkMap S e a mark (a x)) =
      markedOnePointLaw q A α := by
  have hlabel : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
      (atlasSeedMarkMap S e a mark) = markedOnePointLaw q A α :=
    map_normalized_label_atlasSeedMarkMap_eq_markedOnePointLaw S e a mark α labZ c lam hρ
      hcoord hmark hcube hmarkLaw hindep
  exact physical_normalized_tile_mark_eq_markedOnePointLaw η a lam ha hlaw
    (hlabZ (measurableSet_singleton c)) (atlasSeedMarkMap S e a mark) α hmarkMap hlabel


/-- **Target atlas identification (target analogue).**  The same reduction for the
target physical law `η` on `M`, the target common-label map `b : M → Z`, and the
target mark space `B`. -/
theorem physical_normalized_target_tile_atlasSeedMarkMap_eq_markedOnePointLaw {q : ℕ}
    (S : F.CalibratedLevelSeedPatch u) (e : S.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (b : M → Z) {B : Type*} [MeasurableSpace B] (mark : Z → B) (β : Measure B)
    (labZ : Z → ι) (hlabZ : Measurable labZ) (c : ι)
    (η : Measure M) [IsProbabilityMeasure η] (lam : Measure Z) [IsProbabilityMeasure lam]
    (hb : Measurable b) (hlaw : η.map b = lam)
    (hρ : lam (labZ ⁻¹' {c}) ≠ 0)
    (hmarkMap : Measurable (atlasSeedMarkMap S e b mark))
    (hcoord : Measurable (atlasSeedCoord S e b)) (hmark : Measurable mark)
    (hcube : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedCoord S e b) = cubeMeasure (Fin q) 1)
    (hmarkLaw : ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c})).map
        (atlasSeedMark mark) = β)
    (hindep : IndepFun (atlasSeedCoord S e b) (atlasSeedMark mark)
      ((lam (labZ ⁻¹' {c}))⁻¹ • lam.restrict (labZ ⁻¹' {c}))) :
    ((η (b ⁻¹' (labZ ⁻¹' {c})))⁻¹ • η.restrict (b ⁻¹' (labZ ⁻¹' {c}))).map
        (fun y => atlasSeedMarkMap S e b mark (b y)) =
      markedOnePointLaw q B β :=
  physical_normalized_tile_atlasSeedMarkMap_eq_markedOnePointLaw S e b mark β labZ hlabZ c
    η lam hb hlaw hρ hmarkMap hcoord hmark hcube hmarkLaw hindep

end PhysicalAtlas

end OTSelector.Probability
