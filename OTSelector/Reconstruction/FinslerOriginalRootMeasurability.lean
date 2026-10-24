import OTSelector.Reconstruction.FinslerOriginalRootMassUnit

/-!
# Ambient-kernel measurability transfer for the atlas transport

The atlas change of measure of FinslerOriginalAtlasSceneBridge.lean evaluates the
frozen root functionals at the original seed label of each population root, so it
needs the measurability of

  w |-> F (a (curve w 0))

on the whole covector kernel (not only on the seed label subtype), against the
pushforward of the population root law under the extended seed inverse label.  A
prior module proved only the measurable-embedding statement on the label subtype.

This module proves the ambient-kernel transfer.

## 1. Concentration of the pushed piece measure on the actual seed labels

* map_populationSeedRootLabelValue_labels_compl_eq_zero: the pushed piece measure
  charges no complement of the seed label set.  On a selected piece the extended
  seed inverse returns an actual seed label, so the pushed measure is concentrated
  on the seed labels.

## 2. The ambient-kernel transfer

* aestronglyMeasurable_comp_seedLabelRoot: for a measurable root functional
  H : Z -> R and any measure v whose pushforward under the seed inverse is
  concentrated on the seed labels, the ambient composite
  w |-> H (a (curve w 0)) is AEStronglyMeasurable for that pushforward.
  The measurable comparison is the measurable extension of H along the label
  embedding.

## 3. The functional form of the hAmeas/hRmeas side conditions

* aestronglyMeasurable_pieceHaarRootReadout: the Haar density power times a root
  functional evaluated at the seed label root is AEStronglyMeasurable for the
  pushed piece measure;
* hAmeas_of_measurable_root and hRmeas_of_measurable_root: the two side
  conditions of the atlas bridge hold as soon as the corresponding frozen root
  functional is measurable in the root variable.  This is the exact residual:
  root-variable measurability of the frozen coefficient, probe and matching data.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  [Fintype ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {K : Set M}

/-- The seed label set of a calibrated seed patch is Borel. -/
theorem measurableSet_seedPatch_labels
    (Seed : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    MeasurableSet (Seed j).seed.labels :=
  (Seed j).seed.labels_measurable

/-! ## 1. Concentration of the pushed piece measure on the actual seed labels -/

/-- **The pushed piece measure is concentrated on the actual seed labels.**

On a selected population root piece the extended seed inverse returns the actual
seed label of the piece, hence the pushforward of the restricted population root
law under it charges no complement of the seed label set. -/
theorem map_populationSeedRootLabelValue_labels_compl_eq_zero
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAmbientLabelConcMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) :
    ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a))
      ((Seed j).seed.labelsᶜ) = 0 := by
  have hlabel : MeasurableSet (Seed j).seed.labels :=
    measurableSet_seedPatch_labels Seed j
  have hr : Measurable (populationSeedRootLabelValue (Seed j).seed a) :=
    measurable_populationSeedRootLabelValue (Seed j).seed hF hcomplete hu ha hinj
  have hsub : ∀ z, z ∈ populationSeedRootPiece Seed a κ lambda j →
      populationSeedRootLabelValue (Seed j).seed a z ∈ (Seed j).seed.labels := by
    intro z hzp
    rw [populationSeedRootLabelValue_on_piece (a := a) (P := Seed) (κ := κ)
      (lambda := lambda) hF hcomplete hu ha hinj j ⟨z, hzp⟩]
    exact (populationSeedPieceLabel Seed a κ lambda j ⟨z, hzp⟩).property
  have hempty : populationSeedRootPiece Seed a κ lambda j ∩
      populationSeedRootLabelValue (Seed j).seed a ⁻¹' (Seed j).seed.labelsᶜ = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    rintro ⟨z, hzp, hzn⟩
    rw [Set.mem_preimage, Set.mem_compl_iff] at hzn
    exact hzn (hsub z hzp)
  rw [Measure.map_apply hr hlabel.compl, Measure.restrict_apply (hr hlabel.compl),
    Set.inter_comm, hempty, measure_empty]

/-! ## 2. The ambient-kernel transfer -/

/-- **Ambient-kernel measurability transfer for the seed label root.**

For a measurable root functional on the population root space, the composite
w |-> H (a (curve w 0)) on the whole covector kernel is AEStronglyMeasurable for
the pushforward of any measure under the extended seed inverse, provided that
pushforward is concentrated on the actual seed labels.  The measurable comparison
function is the measurable extension of the label-subtype composite along the
subtype embedding; concentration makes the two agree almost everywhere. -/
theorem aestronglyMeasurable_comp_seedLabelRoot
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAmbientTransferMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {ν : Measure Z} (H : Z → ℝ) (hH : Measurable H)
    (hconc : (ν.map (populationSeedRootLabelValue (Seed j).seed a))
      ((Seed j).seed.labelsᶜ) = 0) :
    AEStronglyMeasurable
      (fun w : (Seed j).seed.covector.ker ↦ H (seedLabelRoot Seed a j w))
      (ν.map (populationSeedRootLabelValue (Seed j).seed a)) := by
  have hlabel : MeasurableSet (Seed j).seed.labels :=
    measurableSet_seedPatch_labels Seed j
  have he : MeasurableEmbedding
      ((↑) : (Seed j).seed.labels → (Seed j).seed.covector.ker) :=
    MeasurableEmbedding.subtype_coe hlabel
  have hemb := measurableEmbedding_populationSeedLabel (Seed j).seed hF hcomplete hu ha hinj
  have hg : Measurable
      (fun x : (Seed j).seed.labels ↦ H (a ((Seed j).seed.curve x 0))) :=
    hH.comp hemb.measurable
  have hK : Measurable (extend
      ((↑) : (Seed j).seed.labels → (Seed j).seed.covector.ker)
      (fun x : (Seed j).seed.labels ↦ H (a ((Seed j).seed.curve x 0)))
      (fun _ ↦ (0 : ℝ))) :=
    he.measurable_extend hg measurable_const
  have hae : ∀ᵐ w ∂(ν.map (populationSeedRootLabelValue (Seed j).seed a)),
      w ∈ (Seed j).seed.labels := by
    rw [ae_iff]
    exact hconc
  have heq : (fun w : (Seed j).seed.covector.ker ↦ H (seedLabelRoot Seed a j w))
      =ᵐ[(ν.map (populationSeedRootLabelValue (Seed j).seed a))]
      extend ((↑) : (Seed j).seed.labels → (Seed j).seed.covector.ker)
        (fun x : (Seed j).seed.labels ↦ H (a ((Seed j).seed.curve x 0)))
        (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hae] with w hw
    rw [seedLabelRoot]
    exact (he.injective.extend_apply
      (fun x : (Seed j).seed.labels ↦ H (a ((Seed j).seed.curve x 0)))
      (fun _ ↦ (0 : ℝ)) ⟨w, hw⟩).symm
  exact hK.aestronglyMeasurable.congr heq.symm

/-! ## 3. The functional form of the hAmeas/hRmeas side conditions -/

/-- **The Haar density power times a root functional of the seed label root is
AEStronglyMeasurable for the pushed piece measure.**

This is the exact functional shape of both hAmeas and hRmeas of the atlas bridge:
a measurable Haar density factor times a measurable root functional evaluated at
the seed label root. -/
theorem aestronglyMeasurable_pieceHaarRootReadout
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instPieceReadoutMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {q : ℝ} (hq : 0 < q)
    (H : Z → ℝ) (hH : Measurable H) :
    AEStronglyMeasurable
      (fun w : (Seed j).seed.covector.ker ↦
        (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
          H (seedLabelRoot Seed a j w))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)) :=
  (measurable_ennreal_toReal_rpow_neg
      (measurable_populationSeedPieceHaarDensity Seed a κ lambda hF hcomplete hu ha hinj j)
      hq).aestronglyMeasurable.mul
    (aestronglyMeasurable_comp_seedLabelRoot Seed a hF hcomplete hu ha hinj j H hH
      (map_populationSeedRootLabelValue_labels_compl_eq_zero Seed a κ lambda
        hF hcomplete hu ha hinj j))


/-- **The hAmeas side condition of the atlas bridge holds as soon as the frozen
atlas root integrand is measurable in the root variable.**

The bridge assumes AEStronglyMeasurable of the Haar density power times the atlas
frozen root integrand evaluated at the seed label root.  This is exactly the
general transfer of this module at the root functional given by the atlas frozen
integrand. -/
theorem hAmeas_of_measurable_root
    (α β : Measure UnitMark)
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Mat : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → StationaryForwardMatching α β)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instHAmeasMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {q : ℝ} (hq : 2 < q) (t : ℝ) (f : (K × K) →ᵇ ℝ)
    (hH : Measurable
      (atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j)) :
    AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j
          (a ((Seed j).seed.curve w 0)))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)) :=
  aestronglyMeasurable_pieceHaarRootReadout Seed a κ lambda hF hcomplete hu ha hinj j
    (by linarith : (0 : ℝ) < q)
    (atlasRootFrozenIntegrand α β Seed a κ lambda Acoef fprobe Mat q t f j) hH

/-- **The hRmeas side condition of the atlas bridge holds as soon as the frozen
Palm readout is measurable in the root variable.**

The bridge assumes AEStronglyMeasurable of the Haar density power times the
physical Palm readout of the frozen edge functional at the seed label root.  This
is the general transfer of this module at the root functional given by that
readout. -/
theorem hRmeas_of_measurable_root
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Acoef : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z → ℝ → ℝ → ℝ)
    (fprobe : ((K × K) →ᵇ ℝ) → ℝ → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instHRmeasMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) {q : ℝ} (hq : 2 < q) (t : ℝ) (f : (K × K) →ᵇ ℝ)
    {Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (hH : Measurable (fun z : Z ↦ rootedScenePalmReadout Q
      (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))))) :
    AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity Seed a κ lambda j w).toReal ^ (-2 / q) *
        rootedScenePalmReadout Q
          (rootedSceneFrozenEdge ((Acoef f t) j (a ((Seed j).seed.curve w 0)))
            ((fprobe f t) j (a ((Seed j).seed.curve w 0)))
            (t * populationAtlasTheta Seed a κ lambda j
              (a ((Seed j).seed.curve w 0)) ^ (2 / q))))
      ((lambda.restrict (populationSeedRootPiece Seed a κ lambda j)).map
        (populationSeedRootLabelValue (Seed j).seed a)) :=
  aestronglyMeasurable_pieceHaarRootReadout Seed a κ lambda hF hcomplete hu ha hinj j
    (by linarith : (0 : ℝ) < q)
    (fun z : Z ↦ rootedScenePalmReadout Q
      (rootedSceneFrozenEdge ((Acoef f t) j z) ((fprobe f t) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)))) hH

end OTSelector.Reconstruction