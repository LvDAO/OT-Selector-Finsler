import OTSelector.Reconstruction.FinslerOriginalGlobalRootRefinement

/-!
# The parent chart producer from the window family

This file addresses the two remaining producer gaps of
`FinslerOriginalGlobalRootRefinement.lean`: (i) where the per-parent
`ParentChartProducer` data comes from at the atlas level, and (iii) the
label-reference-law match `hlabref`.

## (i) The atlas-level field supplied by the paper

The window family already supplies, for every window index `j`, its seed patch
`(P j).seed`.  More importantly the seed patch carries a C11 level-seed
presentation (`c11_presentation`), from which we extract the chart label domain,
the section `position`, the ambient curve family `ambient`, and the identities

* `windowSeed_labels_eq`: `(P j).seed.labels = openLabels ∩ position ⁻¹' core`;
* `windowSeed_curve_eq`: `(P j).seed.curve w t = ambient (position w) t`.

Thus the parent seed patch, its labels and its curves are **already determined by
the window family**.  The single atlas-level field the paper supplies that the
window family does not retain is the *chart datum together with the compact
parent core and the linear identification of the window seed label space with the
chart label space*: this is `WindowChartData`.  We construct the full
`ParentChartProducer` from it (`WindowChartData.toParentChartProducer`),
so the producer gap is exactly one datum per window: chart datum + compact core +
linear label identification (with its label and curve equations).

## (iii) The label-reference-law match

`labelTransportMap` is the linear label identification between a refined patch
and its parent window seed, `ψ w = e₀⁻¹ (e w)`; `labelTransportSubtype` restricts
it to the label sets (using that refined cores sit inside the parent core).
`populationSeedLabelReference_eq_of_labelTransport` proves that when the parent
label reference is the pushforward of the refined one along this identification,
the two pushed label reference laws are equal — exactly `hlabref`.
`labelReference_eq_of_windowChartData` is the same statement in the concrete
window-chart-data coordinates.

## Assembly

`rootPieceRefinement_of_windowChartData` feeds the produced
`ParentChartProducer` and the transported label reference laws into
`rootPieceRefinement_of_chartProducer`, yielding the global root-piece
refinement together with its C(a) restriction sums and C(b) exact-one-window
forms.  No producer field beyond `WindowChartData` and the label-measure
transport remains.

## Exact remaining sub-gap

The atlas theorem `exists_global_refinedBallCore_atlas` is a pure selection
principle (its hypothesis is `∀ _, ∃ W, True` and it returns the provided
windows), so it cannot supply `WindowChartData`; the chart datum and compact
core must come from the pre-atlas rational chart construction.  This file
therefore makes `WindowChartData` the precise missing atlas-level field and
proves everything downstream of it.
-/
open Set Function MeasureTheory Manifold OTSelector.Geometry
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## (i) What the window family already supplies -/

/-- The C11 level-seed presentation of the seed patch of each window, extracted
classically from the nonempty presentation field. -/
def windowSeedPresentation (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    ContinuousFinslerNorm.C11LevelSeedPresentation F u (P j).seed.covector (P j).seed.level
      (P j).seed.openLabels (P j).seed.labels (P j).seed.curve :=
  Classical.choice (P j).seed.c11_presentation

/-- **The window seed's labels are a level-section preimage** in its own chart
presentation. -/
theorem windowSeed_labels_eq (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    (P j).seed.labels = (P j).seed.openLabels ∩
      (windowSeedPresentation P j).position ⁻¹' (windowSeedPresentation P j).core :=
  (windowSeedPresentation P j).labels_eq

/-- **The window seed's curves are the ambient curves** composed with the section
of its own chart presentation. -/
theorem windowSeed_curve_eq (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    ∀ (w : (P j).seed.covector.ker) (t : ℝ),
      (P j).seed.curve w t =
        (windowSeedPresentation P j).ambient ((windowSeedPresentation P j).position w) t :=
  fun w t => congrFun (congrFun (windowSeedPresentation P j).curve_eq w) t

/-- **The single atlas-level field missing from the window family.**  A chart datum
per window, a compact parent core inside its open chart domain, and the linear
identification of the window seed's label space with the chart label space,
realizing the window seed's labels and curves through the chart section. -/
structure WindowChartData (P : ℕ → F.CalibratedSeedWindow u) where
  chartData : (j : ℕ) → CoreSectionChartData F u
  parentCore : (j : ℕ) → Set E
  parentCore_compact : ∀ j, IsCompact (parentCore j)
  parentCore_subset : ∀ j, parentCore j ⊆ (chartData j).U
  parentCore_center : ∀ j, (chartData j).σ 0 ∈ parentCore j
  parentEquiv : (j : ℕ) → (P j).seed.covector.ker ≃L[ℝ] (chartData j).p.ker
  parent_labels : ∀ j, (P j).seed.labels =
    (parentEquiv j) ⁻¹' ((chartData j).V ∩ (chartData j).σ ⁻¹' (parentCore j))
  parent_curves : ∀ j (w : (P j).seed.covector.ker) (t : ℝ),
    (P j).seed.curve w t = (chartData j).Γ ((chartData j).σ ((parentEquiv j) w)) t

/-- **From the atlas-level window chart field to the full per-parent producer
map.**  The parent patch is the window's own seed. -/
def WindowChartData.toParentChartProducer {P : ℕ → F.CalibratedSeedWindow u}
    (W : WindowChartData P) : ParentChartProducer F u P where
  chartData := W.chartData
  parentCore := W.parentCore
  parentCore_compact := W.parentCore_compact
  parentCore_subset := W.parentCore_subset
  parentCore_center := W.parentCore_center
  parentPatch := fun j => (P j).seed
  parentEquiv := W.parentEquiv
  parent_labels := W.parent_labels
  parent_curves := W.parent_curves
  seed_eq := fun j => rfl

/-! ## (iii) Label-reference transport along the linear identification -/

/-- **The linear label transport** from a refined patch's label space to its parent
window seed's label space: `ψ w = e₀⁻¹ (e w)`. -/
def labelTransportMap {P : ℕ → F.CalibratedSeedWindow u} (W : WindowChartData P)
    (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ j i, (A j i).covector.ker ≃L[ℝ] (W.chartData j).p.ker)
    (j i : ℕ) (w : (A j i).covector.ker) : (P j).seed.covector.ker :=
  (W.parentEquiv j).symm ((e j i) w)

/-- **The label transport restricted to label sets.**  A label of the refined patch
is a label of the parent window seed, because the refined core sits inside the
parent core. -/
def labelTransportSubtype {P : ℕ → F.CalibratedSeedWindow u} (W : WindowChartData P)
    (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ j i, (A j i).covector.ker ≃L[ℝ] (W.chartData j).p.ker)
    (hAlab : ∀ j i, (A j i).labels = (e j i) ⁻¹'
      ((W.chartData j).V ∩ (W.chartData j).σ ⁻¹'
        (W.parentCore j ∩ closedBall ((W.chartData j).σ 0) (i : ℝ))))
    (j i : ℕ) (w : (A j i).labels) : (P j).seed.labels :=
  ⟨labelTransportMap W A e j i (w : (A j i).covector.ker), by
    rw [W.parent_labels j]
    set w' : (A j i).covector.ker := (w : (A j i).covector.ker)
    have hmem : w' ∈ (A j i).labels := by
      rw [show w' = (w : (A j i).covector.ker) from rfl]
      exact w.property
    have hmem' : (e j i) w' ∈
        (W.chartData j).V ∩ (W.chartData j).σ ⁻¹'
          (W.parentCore j ∩ closedBall ((W.chartData j).σ 0) (i : ℝ)) := by
      have h := hmem
      rw [hAlab j i] at h
      exact h
    have hw : (e j i) (w : (A j i).covector.ker) ∈
        (W.chartData j).V ∩ (W.chartData j).σ ⁻¹'
          (W.parentCore j ∩ closedBall ((W.chartData j).σ 0) (i : ℝ)) := by
      rw [show (w : (A j i).covector.ker) = w' from rfl]
      exact hmem'
    have hmemK : (e j i) (w : (A j i).covector.ker) ∈
        (W.chartData j).V ∩ (W.chartData j).σ ⁻¹' (W.parentCore j) :=
      ⟨hw.1, hw.2.1⟩
    show (W.parentEquiv j) (labelTransportMap W A e j i (w : (A j i).covector.ker)) ∈
      (W.chartData j).V ∩ (W.chartData j).σ ⁻¹' (W.parentCore j)
    rw [show (W.parentEquiv j) (labelTransportMap W A e j i (w : (A j i).covector.ker)) =
      (e j i) (w : (A j i).covector.ker) from
      ContinuousLinearEquiv.apply_symm_apply (W.parentEquiv j) _]
    exact hmemK⟩

/-- **The linear transport is measurable.** -/
theorem measurable_labelTransportMap {P : ℕ → F.CalibratedSeedWindow u}
    (W : WindowChartData P) (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ j i, (A j i).covector.ker ≃L[ℝ] (W.chartData j).p.ker) (j i : ℕ) :
    Measurable (labelTransportMap W A e j i) :=
  ((W.parentEquiv j).symm.continuous.measurable).comp (e j i).continuous.measurable

/-- **Root-map agreement under the label transport.**  The two root maps agree
because both curves run through the same chart datum. -/
theorem root_eq_of_labelTransport {P : ℕ → F.CalibratedSeedWindow u}
    (W : WindowChartData P) (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ j i, (A j i).covector.ker ≃L[ℝ] (W.chartData j).p.ker)
    (hAcur : ∀ j i (w : (A j i).covector.ker) (t : ℝ),
      (A j i).curve w t = (W.chartData j).Γ ((W.chartData j).σ ((e j i) w)) t)
    (a : M → Z) (j i : ℕ) :
    ∀ w : (A j i).covector.ker,
      a ((A j i).curve w 0) =
        a ((P j).seed.curve (labelTransportMap W A e j i w) 0) := by
  intro w
  rw [hAcur j i w 0, W.parent_curves j (labelTransportMap W A e j i w) 0]
  show a ((W.chartData j).Γ ((W.chartData j).σ ((e j i) w)) 0) = _
  rw [show (W.parentEquiv j) (labelTransportMap W A e j i w) = (e j i) w from
    ContinuousLinearEquiv.apply_symm_apply (W.parentEquiv j) _]

/-- **The label-reference-law match from label-measure transport.**  If the parent
label measure is the pushforward of the refined label measure along the linear
label identification, then the two pushed original label reference laws are
equal. -/
theorem populationSeedLabelReference_eq_of_labelTransport
    (S0 S : F.CalibratedLevelSeedPatch u) {a : M → Z}
    (κ0 : Measure S0.covector.ker) (κ : Measure S.covector.ker)
    (ψ : S.covector.ker → S0.covector.ker) (hψ : Measurable ψ)
    (hroot : ∀ w : S.covector.ker, a (S.curve w 0) = a (S0.curve (ψ w) 0))
    (hmap : ∀ (w : S.covector.ker), w ∈ S.labels → ψ w ∈ S0.labels)
    (hκ : κ0.comap ((↑) : S0.labels → S0.covector.ker) =
      (κ.comap ((↑) : S.labels → S.covector.ker)).map
        (fun w : S.labels => (⟨ψ (w : S.covector.ker), hmap (w : S.covector.ker) w.property⟩ :
          S0.labels)))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    populationSeedLabelReference S a κ = populationSeedLabelReference S0 a κ0 := by
  have hroot0 : MeasurableEmbedding
      (fun w : S0.labels => a (S0.curve (w : S0.covector.ker) 0)) :=
    measurableEmbedding_populationSeedLabel S0 hF hcomplete hu ha hinj
  have hg : Measurable (fun w : S.labels =>
      (⟨ψ (w : S.covector.ker), hmap (w : S.covector.ker) w.property⟩ : S0.labels)) :=
    (hψ.comp measurable_subtype_coe).subtype_mk
  simp only [populationSeedLabelReference, labelReferenceOn]
  have hfun : (fun w : S.labels => a (S.curve (w : S.covector.ker) 0)) =
      (fun w : S0.labels => a (S0.curve (w : S0.covector.ker) 0)) ∘
        (fun w : S.labels => (⟨ψ (w : S.covector.ker),
          hmap (w : S.covector.ker) w.property⟩ : S0.labels)) := by
    funext w
    exact hroot (w : S.covector.ker)
  rw [hfun, ← Measure.map_map hroot0.measurable hg, ← hκ]

/-- **The label-reference match in concrete window-chart-data coordinates.** -/
theorem labelReference_eq_of_windowChartData
    {P : ℕ → F.CalibratedSeedWindow u} (W : WindowChartData P)
    (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ j i, (A j i).covector.ker ≃L[ℝ] (W.chartData j).p.ker)
    (hAlab : ∀ j i, (A j i).labels = (e j i) ⁻¹'
      ((W.chartData j).V ∩ (W.chartData j).σ ⁻¹'
        (W.parentCore j ∩ closedBall ((W.chartData j).σ 0) (i : ℝ))))
    (hAcur : ∀ j i (w : (A j i).covector.ker) (t : ℝ),
      (A j i).curve w t = (W.chartData j).Γ ((W.chartData j).σ ((e j i) w)) t)
    (a : M → Z) (κ0 : ∀ j, Measure (P j).seed.covector.ker)
    (κ : ∀ j i, Measure (A j i).covector.ker)
    (htransport : ∀ j i,
      (κ0 j).comap ((↑) : (P j).seed.labels → (P j).seed.covector.ker) =
      ((κ j i).comap ((↑) : (A j i).labels → (A j i).covector.ker)).map
        (labelTransportSubtype W A e hAlab j i))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    ∀ j i, populationSeedLabelReference (A j i) a (κ j i) =
      populationSeedLabelReference (P j).seed a (κ0 j) := by
  intro j i
  exact populationSeedLabelReference_eq_of_labelTransport (P j).seed (A j i)
    (κ0 j) (κ j i) (labelTransportMap W A e j i) (measurable_labelTransportMap W A e j i)
    (root_eq_of_labelTransport W A e hAcur a j i)
    (fun w hw => (labelTransportSubtype W A e hAlab j i ⟨w, hw⟩).property)
    (htransport j i) hF hcomplete hu ha hinj

/-! ## Assembly: the global root-piece refinement from the atlas-level field -/

/-- **Global root-piece refinement from the atlas-level window chart data.**  The
producer is constructed from `WindowChartData` alone; the label-reference-law match
is proved from the label-measure transport.  The conclusion is the full global
conjunction: cover and subset of every parent reference-root set, pairwise
disjointness of the global refined pieces, block cover, the global C(b)
exact-one-window form, and the per-parent and global lambda-level C(a)
restriction sums. -/
theorem rootPieceRefinement_of_windowChartData
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (a : M → Z)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {P : ℕ → F.CalibratedSeedWindow u} (W : WindowChartData P)
    (A : ℕ → ℕ → F.CalibratedLevelSeedPatch u)
    (e : ∀ j i, (A j i).covector.ker ≃L[ℝ] (W.chartData j).p.ker)
    (hAlab : ∀ j i, (A j i).labels = (e j i) ⁻¹'
      ((W.chartData j).V ∩ (W.chartData j).σ ⁻¹'
        (W.parentCore j ∩ closedBall ((W.chartData j).σ 0) (i : ℝ))))
    (hAcur : ∀ j i (w : (A j i).covector.ker) (t : ℝ),
      (A j i).curve w t = (W.chartData j).Γ ((W.chartData j).σ ((e j i) w)) t)
    (κ0 : ∀ j, Measure (P j).seed.covector.ker)
    (κ : ∀ j i, Measure (A j i).covector.ker) (lambda : Measure Z)
    (htransport : ∀ j i,
      (κ0 j).comap ((↑) : (P j).seed.labels → (P j).seed.covector.ker) =
      ((κ j i).comap ((↑) : (A j i).labels → (A j i).covector.ker)).map
        (labelTransportSubtype W A e hAlab j i))
    (hmeasS : ∀ j, MeasurableSet (parentRefRootSets (W.toParentChartProducer) a κ0 lambda j))
    (hmeasR : ∀ j i, MeasurableSet (refinedRefRootSets A a κ lambda j i)) :
    (∀ j, parentRefRootSets (W.toParentChartProducer) a κ0 lambda j ⊆
      ⋃ i, refinedRefRootSets A a κ lambda j i) ∧
    (∀ j i, refinedRefRootSets A a κ lambda j i ⊆
      parentRefRootSets (W.toParentChartProducer) a κ0 lambda j) ∧
    Pairwise (Function.onFun Disjoint (fun n => globalRefinedRootPiece
      (parentRefRootSets (W.toParentChartProducer) a κ0 lambda)
      (refinedRefRootSets A a κ lambda) n)) ∧
    (∀ j, disjointed (parentRefRootSets (W.toParentChartProducer) a κ0 lambda) j ⊆
      ⋃ n ∈ {n | globalRefinedParent n = j},
        globalRefinedRootPiece (parentRefRootSets (W.toParentChartProducer) a κ0 lambda)
          (refinedRefRootSets A a κ lambda) n) ∧
    (∀ j z, z ∈ disjointed (parentRefRootSets (W.toParentChartProducer) a κ0 lambda) j →
      ∃! n, globalRefinedParent n = j ∧ z ∈ globalRefinedRootPiece
        (parentRefRootSets (W.toParentChartProducer) a κ0 lambda)
        (refinedRefRootSets A a κ lambda) n) ∧
    (∀ j, lambda.restrict (disjointed (parentRefRootSets (W.toParentChartProducer) a κ0 lambda) j) =
      Measure.sum (fun i => lambda.restrict (refinedBlockPiece
        (parentRefRootSets (W.toParentChartProducer) a κ0 lambda)
        (refinedRefRootSets A a κ lambda) j i))) ∧
    (lambda.restrict (⋃ j, disjointed (parentRefRootSets (W.toParentChartProducer) a κ0 lambda) j) =
      Measure.sum (fun n => lambda.restrict (globalRefinedRootPiece
        (parentRefRootSets (W.toParentChartProducer) a κ0 lambda)
        (refinedRefRootSets A a κ lambda) n))) := by
  exact rootPieceRefinement_of_chartProducer W.toParentChartProducer A e hAlab hAcur
    a κ0 κ lambda
    (labelReference_eq_of_windowChartData W A e hAlab hAcur a κ0 κ htransport
      hF hcomplete hu ha hinj)
    hmeasS hmeasR

end OTSelector.Reconstruction
