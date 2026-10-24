import OTSelector.Reconstruction.FinslerPopulationSeedIntensityCore

/-!
# Compact cores with continuous, finite, positive original Haar intensity

The positivity and finite bounds are obtained by discarding arbitrarily little
original root mass. The original Haar measure and both conditional laws remain
the references for every later localization.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

private theorem continuousOn_image_of_compact_injOn
    {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace T] {K : Set X} (hK : IsCompact K) {r : X → Y} {d : Y → T}
    (hr : ContinuousOn r K) (hinj : InjOn r K)
    (hd : ContinuousOn (d ∘ r) K) : ContinuousOn d (r '' K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he := (continuousOn_iff_continuous_domRestrict.mp hr).isClosedEmbedding
    (fun x y h ↦ Subtype.ext (hinj x.property y.property h))
  have himage : (fun z : K ↦ r z) '' univ = r '' K := by
    ext y
    simp
  rw [← himage]
  change ContinuousOn d (K.domRestrict r '' univ)
  exact he.isEmbedding.isInducing.continuousOn_image_iff.mpr
    (continuousOn_iff_continuous_domRestrict.mp hd).continuousOn

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- A retained portion of the original root law with continuous actual labels and
continuous, uniformly positive finite Haar intensity. All masses are original masses. -/
structure PopulationSeedIntensityCore
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (j : ℕ) (H : Set Z) (ε : ℝ≥0∞) where
  roots : Set Z
  roots_subset : roots ⊆ H
  roots_subset_piece : roots ⊆ populationSeedRootPiece P a κ lambda j
  compact : IsCompact roots
  small_loss : lambda (H \ roots) < ε
  continuous_label : ContinuousOn (populationSeedRootLabelValue (P j).seed a) roots
  compact_labels : IsCompact (populationSeedRootLabelValue (P j).seed a '' roots)
  labels_subset : populationSeedRootLabelValue (P j).seed a '' roots ⊆ (P j).seed.labels
  root_identity : ∀ z ∈ roots,
    a ((P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) 0) = z
  continuous_density : ContinuousOn
    (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal)
    (populationSeedRootLabelValue (P j).seed a '' roots)
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  bounds : ∀ w ∈ populationSeedRootLabelValue (P j).seed a '' roots,
    lower ≤ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ∧
      (populationSeedPieceHaarDensity P a κ lambda j w).toReal ≤ upper
  finite_density : ∀ z ∈ roots, populationSeedPieceRootDensity P a κ lambda j z < (∞ : ℝ≥0∞)
  reciprocal : ∀ z ∈ roots, populationSeedPieceRootDensity P a κ lambda j z =
    ((populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z)⁻¹

/-- Retain all actual intensity data while taking the retained roots themselves as
the reference set. This changes no measure or density. -/
def PopulationSeedIntensityCore.onOwnRoots
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {j : ℕ} {H : Set Z} {ε : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H ε) :
    PopulationSeedIntensityCore P a κ lambda j D.roots 1 :=
  { D with roots_subset := Subset.rfl
           small_loss := by simp }

/-- Further compact restriction retains the same original density, bounds and
Radon--Nikodym identity on the smaller actual coordinate image. -/
def PopulationSeedIntensityCore.restrictRoots
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {j : ℕ} {H : Set Z} {ε : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H ε)
    {K : Set Z} (hK : IsCompact K) (hsub : K ⊆ D.roots) :
    PopulationSeedIntensityCore P a κ lambda j K 1 where
  roots := K
  roots_subset := Subset.rfl
  roots_subset_piece := hsub.trans D.roots_subset_piece
  compact := hK
  small_loss := by simp
  continuous_label := D.continuous_label.mono hsub
  compact_labels := hK.image_of_continuousOn (D.continuous_label.mono hsub)
  labels_subset := (image_mono hsub).trans D.labels_subset
  root_identity := fun z hz ↦ D.root_identity z (hsub hz)
  continuous_density := D.continuous_density.mono (image_mono hsub)
  lower := D.lower
  upper := D.upper
  lower_pos := D.lower_pos
  lower_le_upper := D.lower_le_upper
  bounds := fun w hw ↦ D.bounds w (image_mono hsub hw)
  finite_density := fun z hz ↦ D.finite_density z (hsub hz)
  reciprocal := fun z hz ↦ D.reciprocal z (hsub hz)

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  [IsFiniteMeasure lambda]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instIntensityCompactMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Every measurable part of an original selected piece admits a large compact
core with continuous original intensity and internal positive finite bounds. -/
theorem exists_populationSeedIntensityCore
    (j : ℕ) [SigmaFinite (κ j)] {H : Set Z} (hH : MeasurableSet H)
    (hsub : H ⊆ populationSeedRootPiece P a κ lambda j)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    Nonempty (PopulationSeedIntensityCore P a κ lambda j H ε) := by
  let r := populationSeedRootLabelValue (P j).seed a
  let d := populationSeedPieceRootDensity P a κ lambda j
  let b := (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda
  let good : Set Z := {z | 0 < d z ∧ d z < (∞ : ℝ≥0∞) ∧ d z = (b z)⁻¹}
  have hd : Measurable d := Measure.measurable_rnDeriv _ _
  have hb : Measurable b := Measure.measurable_rnDeriv _ _
  have hg : MeasurableSet good :=
    (measurableSet_lt measurable_const hd).inter
      ((measurableSet_lt hd measurable_const).inter (measurableSet_eq_fun hd hb.inv))
  have hgood : ∀ᵐ z ∂lambda, z ∈ H → z ∈ good := by
    have h := (ae_restrict_iff'
      (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)).mp
      (ae_populationSeedPieceRootDensity_inv P a κ lambda hF hcomplete hu ha hinj j)
    exact h.mono fun z hz hzH ↦ hz (hsub hzH)
  have hr : Measurable r :=
    measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj
  obtain ⟨K, hKsub, hK, hsmall, hcont⟩ := exists_lusin_compact_core
    (μ := lambda) (hH.inter hg) (measure_ne_top _ _) (hr.prodMk hd.ennreal_toReal) hε
  have hmass : lambda (H \ K) < ε := by
    have heq : (H \ K : Set Z) =ᵐ[lambda] ((H ∩ good) \ K : Set Z) := by
      exact hgood.mono fun z hz ↦ propext
        ⟨fun h ↦ ⟨⟨h.1, hz h.1⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩
    rw [measure_congr heq]
    exact hsmall
  have hKr : K ⊆ populationSeedRootPiece P a κ lambda j :=
    fun z hz ↦ hsub (hKsub hz).1
  have hKrcont : ContinuousOn r K := hcont.fst
  have hKdcont : ContinuousOn (fun z ↦ (d z).toReal) K := hcont.snd
  have hroot : ∀ z ∈ K, a ((P j).seed.curve (r z) 0) = z := by
    intro z hz
    dsimp only [r]
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hKr hz⟩]
    exact populationSeedPieceLabel_root P a κ lambda j ⟨z, hKr hz⟩
  have hcoords (z : Z) (hz : z ∈ K) :
      populationSeedPieceHaarDensity P a κ lambda j (r z) = d z :=
    populationSeedPieceHaarDensity_at_root P a κ lambda hF hcomplete hu ha hinj j (hKr hz)
  have hlabelsub : r '' K ⊆ (P j).seed.labels := by
    rintro _ ⟨z, hz, rfl⟩
    dsimp only [r]
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hKr hz⟩]
    exact (populationSeedPieceLabel P a κ lambda j ⟨z, hKr hz⟩).property
  have hcoordinateCont : ContinuousOn
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal) (r '' K) := by
    apply continuousOn_image_of_compact_injOn hK hKrcont
      (fun x hx y hy h ↦ (hroot x hx).symm.trans ((congrArg
        (fun w ↦ a ((P j).seed.curve w 0)) h).trans (hroot y hy)))
    exact hKdcont.congr (fun z hz ↦ congrArg ENNReal.toReal (hcoords z hz))
  obtain ⟨c, hc, hcle⟩ := hK.exists_forall_le' hKdcont
    (fun z hz ↦ ENNReal.toReal_pos (hKsub hz).2.1.ne' (hKsub hz).2.2.1.ne)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hKdcont
  refine ⟨{
    roots := K
    roots_subset := fun z hz ↦ (hKsub hz).1
    roots_subset_piece := hKr
    compact := hK
    small_loss := hmass
    continuous_label := hKrcont
    compact_labels := hK.image_of_continuousOn hKrcont
    labels_subset := hlabelsub
    root_identity := hroot
    continuous_density := hcoordinateCont
    lower := c
    upper := max c C
    lower_pos := hc
    lower_le_upper := le_max_left _ _
    bounds := ?_
    finite_density := fun z hz ↦ (hKsub hz).2.2.1
    reciprocal := fun z hz ↦ (hKsub hz).2.2.2
  }⟩
  rintro w ⟨z, hz, rfl⟩
  rw [hcoords z hz]
  exact ⟨hcle z hz, (hC (mem_image_of_mem _ hz)).trans (le_max_right _ _)⟩

/-- On the retained compact coordinates the original law has a continuous real
intensity with the internally obtained positive finite bounds. -/
theorem PopulationSeedIntensityCore.coordinateLaw_eq_ofReal
    {j : ℕ} [SigmaFinite (κ j)] {H : Set Z} {ε : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H ε) :
    (lambda.restrict D.roots).map (populationSeedRootLabelValue (P j).seed a) =
      ((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' D.roots)).withDensity
        (fun w ↦ ENNReal.ofReal (populationSeedPieceHaarDensity P a κ lambda j w).toReal) := by
  rw [map_populationSeedCore_eq_withDensity P a κ lambda hF hcomplete hu ha hinj j
    D.compact.measurableSet D.roots_subset_piece]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem D.compact_labels.measurableSet] with w hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [populationSeedPieceHaarDensity_at_root P a κ lambda hF hcomplete hu ha hinj j
    (D.roots_subset_piece hz)]
  exact (ENNReal.ofReal_toReal (D.finite_density z hz).ne).symm

end OTSelector.Reconstruction
