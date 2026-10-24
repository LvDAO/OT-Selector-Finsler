import OTSelector.Reconstruction.FinslerOriginalTileDataPopulationInputs

/-!
# Cube coverage of window labels and the conditional mark kernel of the tile model

This module reduces the two remaining interfaces of the upper pressure lane.

## Cube coverage

The cube-cell construction of the tile-data lane discharged the unit-cube image
`himage` of a tile from the single coverage hypothesis

`seedUnitCube q ⊆ e '' (seedLabel '' retainedPiece)`.

Here that coverage is reduced to two genuinely geometric statements, each closer
to the calibrated-window construction:

* `hlabelCover`: the retained seed labels of the window fill the unit cube in the
  normalized seed coordinates, i.e. every `u ∈ (0,1)^q` is the coordinate of an
  actual calibrated seed label;
* `hretain`: every cube-coordinate seed label of the window is retained, i.e. its
  original root belongs to the selected disjoint piece (finite nonzero population
  reference intensity and first-window ownership).

Neither statement is a consequence of absolute continuity of the population laws
alone: `labels` is an arbitrary measurable set of the seed patch, and the
normalized basis `e` is linear, so the relative size and position of the unit
cube and the label image are a genuine window-refinement condition.

## The conditional mark kernel

The measured window atlas does not give independent coordinate and mark: the
exact clock law of a window is a conditional kernel with density
`t ↦ J(t,w) ρ(t,w)` given the seed label `w`.  This module states the correct
mark-law input of the tile model as a joint-law hypothesis

`ρ.map (fun x => (coord x, mark x)) = (ρ.map coord) ⊗ₘ K`

with a Markov mark kernel `K`, proves its joint-mass form (the conditional mark
mass), and proves that it is *equivalent* to the classical independent-mark
inputs of the upper localization (mark marginal `α` plus independence) exactly
when the kernel is almost everywhere constant.  Thus the upper localization's
mark-law hypotheses are the constant-kernel special case of the conditional form,
and the non-constant conditional kernel is the correct general tile-model input.
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

/-! ## Cube coverage of the retained window labels -/

section CubeCoverage

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instCubeCoverageMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **Cube coverage from seed-label coverage and retention.**

If the retained seed labels of window `j` fill the unit cube in the normalized seed
coordinates, and every cube-coordinate seed label of the window is retained in
the selected piece, then the unit cube is contained in the seed-label image of
the retained piece.  This is the coverage hypothesis `hcover` of the cube-cell
construction, reduced to its two geometric components. -/
theorem cubeCoverage_of_seedLabelCover_and_retention (j : ℕ) {q : ℕ}
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (hlabelCover : OTSelector.Probability.seedUnitCube q ⊆
      e '' (P j).seed.labels)
    (hretain : ∀ w ∈ (P j).seed.labels, e w ∈ OTSelector.Probability.seedUnitCube q →
      a ((P j).seed.curve w 0) ∈ populationSeedRootPiece P a κ lambda j) :
    OTSelector.Probability.seedUnitCube q ⊆
      e '' (populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootPiece P a κ lambda j) := by
  intro v hv
  obtain ⟨w, hw, hwe⟩ := hlabelCover hv
  refine ⟨populationSeedRootLabelValue (P j).seed a (a ((P j).seed.curve w 0)),
    ⟨a ((P j).seed.curve w 0), hretain w hw (hwe ▸ hv), rfl⟩, ?_⟩
  rw [populationSeedRootLabelValue_at_label (P j).seed hF hcomplete hu ha hinj ⟨w, hw⟩]
  exact hwe

/-- **Cube coverage from root-domain coverage and retention.**

Variant in terms of the retained root domain: if the unit cube is covered by the
normalized seed labels of the window's root domain and the cube-coordinate roots
are retained in the selected piece, then the coverage hypothesis holds. -/
theorem cubeCoverage_of_rootDomainCover_and_retention (j : ℕ) {q : ℕ}
    (e : (P j).seed.covector.ker ≃L[ℝ] (Fin q → ℝ))
    (hrootCover : OTSelector.Probability.seedUnitCube q ⊆
      e '' (populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootDomain (P j).seed a))
    (hretain : ∀ z ∈ populationSeedRootDomain (P j).seed a,
      e (populationSeedRootLabelValue (P j).seed a z) ∈
        OTSelector.Probability.seedUnitCube q →
      z ∈ populationSeedRootPiece P a κ lambda j) :
    OTSelector.Probability.seedUnitCube q ⊆
      e '' (populationSeedRootLabelValue (P j).seed a ''
        populationSeedRootPiece P a κ lambda j) := by
  intro v hv
  obtain ⟨z, ⟨z', hz', rfl⟩, hzv⟩ := hrootCover hv
  exact ⟨populationSeedRootLabelValue (P j).seed a z',
    ⟨z', hretain z' hz' (by rw [hzv]; exact hv), rfl⟩, hzv⟩

end CubeCoverage

/-! ## The conditional mark kernel of the tile model -/

section ConditionalMark

variable {X Am : Type*} [MeasurableSpace X] [MeasurableSpace Am] {q : ℕ}

/-- **The conditional mark law of a cell.**

The joint law of the normalized cell law under the cube coordinate and the mark is
the composition product of the coordinate law with a mark kernel.  This is the
correct replacement of the independent-product mark input when the mark (clock)
law depends on the coordinate: conditionally on the coordinate `w`, the mark has
law `K w`. -/
def ConditionalMarkLaw (ρ : Measure X) (coord : X → Fin q → ℝ) (mark : X → Am)
    (K : Kernel (Fin q → ℝ) Am) : Prop :=
  ρ.map (fun x => (coord x, mark x)) = (ρ.map coord) ⊗ₘ K

/-- **The conditional mark mass.**  Under the conditional mark law the joint mass
of a coordinate piece and a mark set is the mark kernel integrated against the
coordinate law. -/
theorem conditionalMarkLaw_apply {ρ : Measure X} [IsFiniteMeasure ρ]
    {coord : X → Fin q → ℝ} (hcoord : Measurable coord)
    {mark : X → Am} (hmark : Measurable mark) {K : Kernel (Fin q → ℝ) Am}
    [IsSFiniteKernel K] (hK : ConditionalMarkLaw ρ coord mark K)
    {s : Set (Fin q → ℝ)} (hs : MeasurableSet s) {t : Set Am} (ht : MeasurableSet t) :
    ρ (coord ⁻¹' s ∩ mark ⁻¹' t) = ∫⁻ w in s, K w t ∂(ρ.map coord) := by
  have hpre : (fun x => (coord x, mark x)) ⁻¹' (s ×ˢ t) =
      coord ⁻¹' s ∩ mark ⁻¹' t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
  rw [← hpre, ← Measure.map_apply (hcoord.prodMk hmark) (hs.prod ht), hK,
    Measure.compProd_apply_prod hs ht]

/-- **The mark law under a conditional mark kernel is the mixture of the
conditional kernels.** -/
theorem conditionalMarkLaw_mixture {ρ : Measure X} [IsFiniteMeasure ρ]
    {coord : X → Fin q → ℝ} (hcoord : Measurable coord)
    {mark : X → Am} (hmark : Measurable mark) {K : Kernel (Fin q → ℝ) Am}
    [IsSFiniteKernel K] (hK : ConditionalMarkLaw ρ coord mark K)
    {t : Set Am} (ht : MeasurableSet t) :
    ρ (mark ⁻¹' t) = ∫⁻ w, K w t ∂(ρ.map coord) := by
  have h := conditionalMarkLaw_apply (coord := coord) (mark := mark) hcoord hmark hK
    MeasurableSet.univ ht
  simpa using h

end ConditionalMark

/-! ## Reduction to the independent-mark inputs of the upper localization -/

section ConditionalMarkClassical

variable {X Am : Type*} [MeasurableSpace X] [MeasurableSpace Am] {q : ℕ}

/-- **A constant conditional kernel gives the independent-mark inputs.**  If the
mark kernel is almost everywhere the constant kernel `α`, then the coordinate
and the mark are independent and the mark law is `α`: exactly the two mark-law
hypotheses of the upper pressure localization. -/
theorem markInputs_of_conditionalMarkLaw_const {ρ : Measure X} [IsProbabilityMeasure ρ]
    {coord : X → Fin q → ℝ} (hcoord : Measurable coord)
    {mark : X → Am} (hmark : Measurable mark) {K : Kernel (Fin q → ℝ) Am}
    [IsSFiniteKernel K] (hK : ConditionalMarkLaw ρ coord mark K)
    (α : Measure Am) [IsProbabilityMeasure α]
    (hconst : K =ᵐ[ρ.map coord] Kernel.const (Fin q → ℝ) α) :
    ρ.map mark = α ∧ IndepFun coord mark ρ := by
  haveI : IsProbabilityMeasure (ρ.map coord) :=
    Measure.isProbabilityMeasure_map hcoord.aemeasurable
  have hprod : ρ.map (fun x => (coord x, mark x)) = (ρ.map coord).prod α := by
    rw [hK, Measure.compProd_congr hconst, Measure.compProd_const]
  have hred := three_reductions_of_map_prod_eq_prod hcoord hmark hprod
  exact ⟨hred.2.1, hred.2.2⟩

/-- **The independent-mark inputs are the constant-kernel conditional mark law.**
Conversely, the classical mark law plus independence give the conditional mark law
with the constant kernel `α`. -/
theorem conditionalMarkLaw_const_of_markInputs {ρ : Measure X} [IsFiniteMeasure ρ]
    {coord : X → Fin q → ℝ} (hcoord : Measurable coord)
    {mark : X → Am} (hmark : Measurable mark) {α : Measure Am} [IsProbabilityMeasure α]
    (hmarkLaw : ρ.map mark = α) (hindep : IndepFun coord mark ρ) :
    ConditionalMarkLaw ρ coord mark (Kernel.const (Fin q → ℝ) α) := by
  unfold ConditionalMarkLaw
  rw [(hindep.map_prod_eq_prod_map_map hcoord.aemeasurable hmark.aemeasurable),
    hmarkLaw, Measure.compProd_const]

/-- **The upper-localization mark hypotheses are exactly the constant-kernel
conditional mark law.** -/
theorem conditionalMarkLaw_const_iff_markInputs {ρ : Measure X} [IsProbabilityMeasure ρ]
    {coord : X → Fin q → ℝ} (hcoord : Measurable coord)
    {mark : X → Am} (hmark : Measurable mark) (α : Measure Am) [IsProbabilityMeasure α] :
    ConditionalMarkLaw ρ coord mark (Kernel.const (Fin q → ℝ) α) ↔
      ρ.map mark = α ∧ IndepFun coord mark ρ :=
  ⟨fun hK => markInputs_of_conditionalMarkLaw_const hcoord hmark hK α
      (Filter.EventuallyEq.rfl),
    fun h => conditionalMarkLaw_const_of_markInputs hcoord hmark h.1 h.2⟩

/-- **Bridge to the product-law form of the tile model.**  A conditional mark law
with constant kernel together with the uniform cube-coordinate law gives the joint
product law consumed by the tile-model block comparison. -/
theorem productLaw_of_conditionalMarkLaw_const {ρ : Measure X} [IsProbabilityMeasure ρ]
    {coord : X → Fin q → ℝ} (hcoord : Measurable coord)
    {mark : X → Am} (hmark : Measurable mark)
    (hK : ConditionalMarkLaw ρ coord mark (Kernel.const (Fin q → ℝ) α))
    [IsProbabilityMeasure α]
    (hcube : ρ.map coord = OTSelector.Probability.cubeMeasure (Fin q) 1) :
    ρ.map (fun x => (coord x, mark x)) =
      (OTSelector.Probability.cubeMeasure (Fin q) 1).prod α := by
  have hK' : ρ.map (fun x => (coord x, mark x)) =
      (ρ.map coord) ⊗ₘ Kernel.const (Fin q → ℝ) α := hK
  rw [hK', Measure.compProd_const, hcube]

end ConditionalMarkClassical

end OTSelector.Reconstruction
