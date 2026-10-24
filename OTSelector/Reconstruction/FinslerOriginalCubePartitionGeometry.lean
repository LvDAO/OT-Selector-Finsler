import OTSelector.Reconstruction.FinslerOriginalTileDataPopulationInputs
import OTSelector.Geometry.Finsler.CalibratedSeedWindowFubini

/-!
# Cube-partition geometry and the conditional mark law of the tile atlas

The tile-data reduction
`OTSelector/Reconstruction/FinslerOriginalTileDataPopulationInputs.lean`
left two geometric inputs open: the unit-cube image `himage` of a retained
seed-label cell, and the constancy `hprop` of the population label intensity on
the piece (together with the mark-law product).  This module treats them with
the actual calibrated window geometry.

## The cube cell

For an atlas window with seed basis `e` we define the *cube cell*

`seedCubeCell = populationSeedRootPiece ∩ {z | e (seedLabel z) ∈ (0,1)^q}`

in the common label space.  It is measurable, lies in the retained piece, and
its seed-label image is exactly the unit cube **provided** the unit cube is
contained in the seed-label image of the retained piece.  Thus `himage` is
discharged by construction from the single coverage statement `hcover`, which
is the genuine content of "the window's retained labels cover the cube".

## The exact Haar normalization and the label intensity

`CalibratedSeedWindow.exists_labelHaar_setLIntegral_labelRestriction` gives, for
each window, a label Haar measure `κ` with
`tubeParameterMeasure = volume.prod κ` and an exact time-first integral
representation of the original population law on the window.  Specializing that
identity gives

* the exact **label mass** of every measurable label piece as the double integral
  of the weighted Jacobian `J * ρ` over the clock interval and the label Haar
  measure (the change of variables plus the Haar normalization of the window);
* the exact **joint (label, clock) mass**, which is the mark-law input in its
  correct conditional-kernel form: given the seed label `w`, the clock law has
  density proportional to `t ↦ J(t,w) ρ(t,w)`.

## `hprop` in its correct form

`hprop` is exactly the statement that the Radon--Nikodym density of the
population piece law with respect to the seed Haar reference is almost everywhere
constant.  This module proves that equivalence and identifies the density with
the clock-integrated Jacobian above.  Constancy of that integral (uniform
population intensity) is not a consequence of absolute continuity alone; it is
the single remaining population hypothesis.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open MeasureTheory.Measure
open OTSelector.Probability
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
  unitInterval

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

section CubeCell

/-! ## The cube cell of an atlas window -/

/-- **The cube cell of an atlas window.**  The retained label piece of the window
cut out by the condition that its normalized seed label lies in the unit cube.
This is the canonical choice of a tile cell: it is exactly the part of the piece
whose seed coordinate fills the unit cube. -/
noncomputable def seedCubeCell (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) (j : ℕ)
    {q : ℕ} (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ)) : Set Z :=
  populationSeedRootPiece P a κ lambda j ∩
    (fun z => e (populationSeedRootLabelValue (P j).seed a z)) ⁻¹'
      OTSelector.Probability.seedUnitCube q

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instCubeCellMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The cube cell is measurable. -/
theorem measurableSet_seedCubeCell (j : ℕ) {q : ℕ}
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ)) :
    MeasurableSet (seedCubeCell P a κ lambda j e) := by
  refine (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j).inter ?_
  exact (OTSelector.Probability.measurableSet_seedUnitCube q).preimage
    (e.continuous.measurable.comp
      (measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj))

/-- The cube cell is contained in the retained piece of its window. -/
theorem seedCubeCell_subset_piece (j : ℕ) {q : ℕ}
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ)) :
    seedCubeCell P a κ lambda j e ⊆ populationSeedRootPiece P a κ lambda j :=
  inter_subset_left

/-- **The unit-cube image of the cube cell.**  If the unit cube is contained in the
seed-label image of the retained piece of the window, then the seed-label image of
the cube cell is *exactly* the unit cube.  This discharges the cube-image input
`himage` of the tile data by construction. -/
theorem image_seedCubeCell_eq_seedUnitCube (j : ℕ) {q : ℕ}
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (hcover : OTSelector.Probability.seedUnitCube q ⊆
      e '' (populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootPiece P a κ lambda j)) :
    e '' (populationSeedRootLabelValue (P j).seed a ''
      seedCubeCell P a κ lambda j e) = OTSelector.Probability.seedUnitCube q := by
  ext u
  constructor
  · rintro ⟨w, ⟨z, ⟨-, hz⟩, rfl⟩, rfl⟩
    exact hz
  · intro hu
    obtain ⟨w, ⟨z, hz, rfl⟩, hwu⟩ := hcover hu
    refine ⟨populationSeedRootLabelValue (P j).seed a z, ⟨z, ⟨hz, ?_⟩, rfl⟩, hwu⟩
    change e (populationSeedRootLabelValue (P j).seed a z) ∈
      OTSelector.Probability.seedUnitCube q
    rw [hwu]
    exact hu

end CubeCell

/-! ## Exact Haar normalization of the window law -/

/-- **The actual clock on the calibrated window.**  On a window the original
potential clock reads the parameter time shifted by the seed level, throughout the
retained rational window. -/
theorem window_clock (P : F.CalibratedSeedWindow u) (hF : F.IsSmoothStronglyConvex)
    (hu : let _instWindowClockMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (w : P.seed.covector.ker) (hw : w ∈ P.labels) :
    let _instWindowClockResult : MetricSpace M := F.metricSpace
    ∀ t ∈ Icc (P.left : ℝ) P.right,
      u (P.seed.curve w t) = (P.seed.level : ℝ) + t := by
  let _instWindowClockMetric : MetricSpace M := F.metricSpace
  dsimp only
  intro t ht
  exact (hF.calibrated_window_of_complete_unit_endpoints hu
    (P.seed.complete w hw.1) (P.seed.unit w hw.1) hw.2.1 hw.2.2).1 t ht

/-- **Exact window label mass from the Haar normalization.**

For each calibrated window there is a label Haar measure `κ` such that the tube
parameter measure is the product of Lebesgue time and `κ`, and the original
population mass of every measurable label piece inside the window is the double
integral of the weighted Jacobian `J * ρ` over the clock interval and the label
Haar measure.  This is the exact change of variables together with the Haar
normalization of the window. -/
theorem exists_window_haar_label_mass (P : F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowMassMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (horder : let _instWindowMassOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) [SFinite ν]
    (hνchart : (ν.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source).map
      (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)) ≪ m) :
    ∃ κ : Measure P.seed.covector.ker, IsAddHaarMeasure κ ∧
      tubeParameterMeasure P.seed.normalization m = (volume : Measure ℝ).prod κ ∧
      ∀ (B : Set Z), MeasurableSet B →
        let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
        let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
        ν ((P.toManifold '' P.domain) ∩ a ⁻¹' B) =
          ∫⁻ w in P.seedLabelSlice a B ∩ ball P.center.2 (P.seed.radius P.center),
            ∫⁻ t in Ioo (P.left : ℝ) P.right ∩ ball P.center.1 (P.seed.radius P.center),
              (ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization (t, w)) *
                ρ (P.readout (t, w))) ∂volume ∂κ := by
  obtain ⟨κ, hκ, hprod, hmain⟩ :=
    OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow.exists_labelHaar_setLIntegral_labelRestriction
      P hF hcomplete hu ha horder m ν hνchart
  refine ⟨κ, hκ, hprod, ?_⟩
  intro B hB
  have h := hmain B hB (1 : M → ℝ≥0∞) measurable_one
  simpa only [Pi.one_apply, mul_one, setLIntegral_one] using h

/-- **The mark-law input in its correct conditional-kernel form.**

For each calibrated window there is a label Haar measure `κ` with
`tubeParameterMeasure = volume.prod κ` such that, for every measurable label
piece `B` and every measurable clock set `C`, the joint original population
mass of (label in `B`, clock in `C`) inside the window is the double integral
of the weighted Jacobian over the label slice and the *time set cut out by the
clock condition* `{t | level + t ∈ C}`.

Consequently, conditionally on the seed label `w`, the clock is distributed on
the window clock interval with the explicit density
`t ↦ J(t,w) ρ(t,w)`.  This is the correct conditional-kernel form of the
mark-law input: the mark is not independent of the label in general, because this
density depends on `w` and may vanish. -/
theorem exists_window_haar_clock_kernel (P : F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowKernelMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (horder : let _instWindowKernelOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure] (ν : Measure M) [SFinite ν]
    (hνchart : (ν.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source).map
      (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)) ≪ m) :
    ∃ κ : Measure P.seed.covector.ker, IsAddHaarMeasure κ ∧
      tubeParameterMeasure P.seed.normalization m = (volume : Measure ℝ).prod κ ∧
      ∀ (B : Set Z), MeasurableSet B → ∀ (C : Set ℝ), MeasurableSet C →
        let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
        let ρ := ((ν.restrict χ.source).map χ).rnDeriv m
        ν ((P.toManifold '' P.domain) ∩ a ⁻¹' B ∩ u ⁻¹' C) =
          ∫⁻ w in P.seedLabelSlice a B ∩ ball P.center.2 (P.seed.radius P.center),
            ∫⁻ t in Ioo (P.left : ℝ) P.right ∩ ball P.center.1 (P.seed.radius P.center),
              (ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization (t, w)) *
                ρ (P.readout (t, w))) *
                Set.indicator {t : ℝ | (P.seed.level : ℝ) + t ∈ C} (fun _ => 1) t
                ∂volume ∂κ := by
  obtain ⟨κ, hκ, hprod, hmain⟩ :=
    OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow.exists_labelHaar_setLIntegral_labelRestriction
      P hF hcomplete hu ha horder m ν hνchart
  refine ⟨κ, hκ, hprod, ?_⟩
  intro B hB C hC
  let _instWindowKernelProofMetric : MetricSpace M := F.metricSpace
  dsimp only
  have huC : MeasurableSet (u ⁻¹' C) := hC.preimage hu.continuous.measurable
  have h := hmain B hB ((u ⁻¹' C).indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator huC)
  rw [setLIntegral_indicator huC, setLIntegral_one] at h
  have hset : (u ⁻¹' C) ∩ ((P.toManifold '' P.domain) ∩ a ⁻¹' B) =
      (P.toManifold '' P.domain) ∩ a ⁻¹' B ∩ u ⁻¹' C := by
    rw [Set.inter_comm (u ⁻¹' C), Set.inter_assoc]
  rw [hset] at h
  rw [h]
  have hW : MeasurableSet (P.seedLabelSlice a B ∩ ball P.center.2 (P.seed.radius P.center)) :=
    (P.measurableSet_seedLabelSlice hu ha hB).inter measurableSet_ball
  have hT : MeasurableSet (Ioo (P.left : ℝ) P.right ∩
      ball P.center.1 (P.seed.radius P.center)) := measurableSet_Ioo.inter measurableSet_ball
  refine setLIntegral_congr_fun hW ?_
  intro w hw
  refine setLIntegral_congr_fun hT ?_
  intro t ht
  have htIcc : t ∈ Icc (P.left : ℝ) P.right :=
    ⟨le_of_lt ht.1.1, le_of_lt ht.1.2⟩
  have hclock : u (P.toManifold (t, w)) = (P.seed.level : ℝ) + t :=
    window_clock P hF hu w hw.1.1 t htIcc
  have hmem : P.toManifold (t, w) ∈ u ⁻¹' C ↔ (P.seed.level : ℝ) + t ∈ C := by
    rw [Set.mem_preimage, hclock]
  simp only []
  by_cases hc : (P.seed.level : ℝ) + t ∈ C
  · rw [Set.indicator_of_mem (hmem.mpr hc) (fun _ => (1 : ℝ≥0∞)),
      Set.indicator_of_mem (s := {t : ℝ | (P.seed.level : ℝ) + t ∈ C}) hc
        (fun _ => (1 : ℝ≥0∞))]
  · rw [Set.indicator_of_notMem (fun hh => hc (hmem.mp hh)) (fun _ => (1 : ℝ≥0∞)),
      Set.indicator_of_notMem (s := {t : ℝ | (P.seed.level : ℝ) + t ∈ C}) hc
        (fun _ => (1 : ℝ≥0∞))]

section CubePartition

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instCubePartitionMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-! ## `hprop` in its correct form: constancy of the label intensity -/

/-- **`hprop` is exactly the constancy of the original label intensity.**

The uniform-density hypothesis of the tile data is precisely the statement that
the Radon--Nikodym density of the population piece law with respect to the seed
Haar reference is almost everywhere constant.  By the exact Haar normalization of
the window law this density is the clock-integrated weighted Jacobian
`w ↦ ∫_t J(t,w) ρ(t,w) dt`, so this is the exact form in which the uniform
intensity hypothesis enters; it is not a consequence of absolute continuity
alone. -/
theorem labelRestrict_eq_smul_reference_iff [SigmaFinite lambda]
    (j : ℕ) [SigmaFinite (κ j)] :
    (∃ c : ℝ≥0∞, c ≠ ⊤ ∧
        lambda.restrict (populationSeedRootPiece P a κ lambda j) =
          c • populationSeedLabelReference (P j).seed a (κ j)) ↔
      ∃ c : ℝ≥0∞, c ≠ ⊤ ∧
        populationSeedPieceRootDensity P a κ lambda j
          =ᵐ[populationSeedLabelReference (P j).seed a (κ j)] (fun _ => c) := by
  constructor
  · rintro ⟨c, hctop, hprop⟩
    exact ⟨c, hctop,
      populationSeedPieceRootDensity_const_of_label_law_smul P a κ lambda
        hF hcomplete hu ha hinj j hctop hprop⟩
  · rintro ⟨c, hctop, hconst⟩
    refine ⟨c, hctop, ?_⟩
    have hAC := populationSeedRootPiece_absolutelyContinuous P a κ lambda
      hF hcomplete hu ha hinj j
    haveI hσ : SigmaFinite (populationSeedLabelReference (P j).seed a (κ j)) :=
      sigmaFinite_labelReferenceOn (κ j) (P j).seed.labels_measurable
        (measurableEmbedding_populationSeedLabel (P j).seed hF hcomplete hu ha hinj)
    calc lambda.restrict (populationSeedRootPiece P a κ lambda j)
        = (populationSeedLabelReference (P j).seed a (κ j)).withDensity
            (populationSeedPieceRootDensity P a κ lambda j) :=
          (Measure.withDensity_rnDeriv_eq _ _ hAC).symm
      _ = (populationSeedLabelReference (P j).seed a (κ j)).withDensity (fun _ => c) :=
          withDensity_congr_ae hconst
      _ = c • populationSeedLabelReference (P j).seed a (κ j) :=
          withDensity_const c

/-- **The normalized cube-coordinate law of the canonical cube cell.**

Combining the constructed cube cell with the uniform intensity hypothesis gives
the label-level uniform cube law of the tile data: the normalized label law of the
cube cell, read through the atlas coordinate, is the uniform cube law.  This is
the `hcube` input of the frozen-comparison lane, now stated for the canonical cube
cell rather than for an abstract retained region. -/
theorem cube_cell_normalized_coordinate_law [SigmaFinite lambda]
    (j : ℕ) [SigmaFinite (κ j)] [IsAddHaarMeasure (κ j)]
    {q : ℕ} (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (hcover : OTSelector.Probability.seedUnitCube q ⊆
      e '' (populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootPiece P a κ lambda j))
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hprop : lambda.restrict (populationSeedRootPiece P a κ lambda j) =
      c • populationSeedLabelReference (P j).seed a (κ j)) :
    (lambda (seedCubeCell P a κ lambda j e))⁻¹ •
        (lambda.restrict (seedCubeCell P a κ lambda j e)).map
          (atlasSeedCoord (P j).seed e a) =
      OTSelector.Probability.cubeMeasure (Fin q) 1 :=
  OTSelector.Probability.normalized_seed_coordinate_law_of_atlas_haar
    (P := P) (a := a) (κ := κ) (lambda := lambda) hF hcomplete hu ha hinj j e
    (measurableSet_seedCubeCell P a κ lambda hF hcomplete hu ha hinj j e)
    (seedCubeCell_subset_piece P a κ lambda hF hcomplete hu ha hinj j e) hc0 hctop hprop
    (image_seedCubeCell_eq_seedUnitCube P a κ lambda hF hcomplete hu ha hinj j e hcover)


/-- **Physical normalized cube law of the canonical cube cell.**

This is the tile-data `hcube` input in its final physical form: for the *actual*
population `η` on the constructed cube cell of an atlas window, the normalized
physical cell law of any coordinate that agrees with the atlas cube coordinate on
the cell is the uniform cube law.  It combines the constructed cube cell, the
uniform intensity hypothesis, the Haar normalization and the label-to-physical
cell-law transport. -/
theorem measured_atlas_cube_cell_physical_cube_law [SigmaFinite lambda]
    (j : ℕ) [SigmaFinite (κ j)] [IsAddHaarMeasure (κ j)]
    {q : ℕ} (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (hcover : OTSelector.Probability.seedUnitCube q ⊆
      e '' (populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootPiece P a κ lambda j))
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hprop : lambda.restrict (populationSeedRootPiece P a κ lambda j) =
      c • populationSeedLabelReference (P j).seed a (κ j))
    (η : Measure M) (hηa : η.map a = lambda)
    (coordS : M → Fin q → ℝ)
    (hagree : coordS =ᵐ[η.restrict (a ⁻¹' seedCubeCell P a κ lambda j e)]
      fun x => atlasSeedCoord (P j).seed e a (a x)) :
    ((η (a ⁻¹' seedCubeCell P a κ lambda j e))⁻¹ •
        η.restrict (a ⁻¹' seedCubeCell P a κ lambda j e)).map coordS =
      OTSelector.Probability.cubeMeasure (Fin q) 1 := by
  refine cell_cube_law_of_label_law a ha η lambda hηa
    (measurableSet_seedCubeCell P a κ lambda hF hcomplete hu ha hinj j e)
    coordS (atlasSeedCoord (P j).seed e a)
    (measurable_atlasSeedCoord (P j).seed hF hcomplete hu ha hinj e) ?_ hagree
  rw [Measure.map_smul]
  exact cube_cell_normalized_coordinate_law P a κ lambda hF hcomplete hu ha hinj j e
    hcover hc0 hctop hprop

end CubePartition

end OTSelector.Reconstruction
