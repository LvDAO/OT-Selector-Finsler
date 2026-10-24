import OTSelector.Reconstruction.FinslerCoefficientCoreLocalPressure
import OTSelector.Reconstruction.FinslerCoefficientCorePartition
import OTSelector.Reconstruction.FinslerFiniteTilePressure

/-!
# Actual measurable pressure tiles from the original population core

The retained finite physical core supplies Taylor covers and disjoint root cells.
The resulting edge events are read from the original sample roots and potential
clocks, with no additional balancing or coordinate selection.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Actual finite reference covers and their measurable cells on the same retained
physical population core. -/
structure TaylorTiles (ε : ℝ) where
  cover : ∀ i, (D.haar.continuous.coefficient i).TaylorRootCover ε
  partition : ∀ i, FiniteRootNeighborhoodPartition (D.haar.continuous.coefficient i).roots
    (cover i).centers (cover i).neighborhood

/-- The original local pressure core supplies all finite Taylor tiles without
further restriction of any population or introduction of a remainder hypothesis. -/
theorem nonempty_taylorTiles
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTilesMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {ε : ℝ} (hε : 0 < ε) : Nonempty (D.TaylorTiles ε) := by
  let _instTilesMetric : MetricSpace M := F.metricSpace
  let _instTilesProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instTilesPolish : PolishSpace M := inferInstance
  let cover := fun i ↦ Classical.choice (D.nonempty_taylorRootCover
    hF hcomplete hu ha hinj i hε)
  exact ⟨⟨cover, fun i ↦ Classical.choice (cover i).nonempty_partition⟩⟩

namespace TaylorTiles

variable {D} {ε : ℝ} (T : D.TaylorTiles ε)

/-- A tile remembers both its original seed piece and its root cell. -/
abbrev Index := (i : Fin D.haar.continuous.count) × Fin (T.partition i).count

/-- The original coefficient core used by a tile. -/
def core (k : T.Index) := D.haar.continuous.coefficient k.1

/-- The actual frozen root for a tile. -/
def reference (k : T.Index) : ℚ → M := (T.partition k.1).center k.2

/-- The original sample edge belongs to a tile exactly when both roots lie in its
same cell and their original potential clocks lie in its retained pair window. -/
def edgeEvent {n : ℕ} (X Y : Fin n → M) (k : T.Index) : Set (Fin n × Fin n) :=
  {ij | a (X ij.1) ∈ (T.partition k.1).cell k.2 ∧
    a (Y ij.2) ∈ (T.partition k.1).cell k.2 ∧
    (u (X ij.1), u (Y ij.2)) ∈ (T.core k).window.region}

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M] in
/-- The actual edge events are disjoint across all retained seeds and root cells. -/
theorem edgeEvent_disjoint {n : ℕ} (X Y : Fin n → M) :
    Pairwise (fun k l : T.Index ↦ Disjoint (T.edgeEvent X Y k) (T.edgeEvent X Y l)) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ hne
  apply Set.disjoint_left.mpr
  intro ij hk hl
  by_cases hij : i = j
  · subst j
    have hkl : k ≠ l := fun h ↦ hne (congrArg (Sigma.mk i) h)
    exact Set.disjoint_left.mp ((T.partition i).disjoint hkl) hk.1 hl.1
  · exact Set.disjoint_left.mp (D.haar.continuous.disjoint hij)
      ((T.partition i).cell_subset k hk.1).1 ((T.partition j).cell_subset l hl.1).1

omit [BorelSpace E] in
/-- Measurable physical sample arrays give measurable original tile events. -/
theorem measurable_edgeEvent
    (hu : let _instTileEventMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j)) :
    ∀ k i j, MeasurableSet {ξ | (i, j) ∈ T.edgeEvent (X ξ) (Y ξ) k} := by
  let _instTileEventMetric : MetricSpace M := F.metricSpace
  intro k i j
  exact ((ha.comp (hX i)) ((T.partition k.1).measurable_cell k.2)).inter
    (((ha.comp (hY j)) ((T.partition k.1).measurable_cell k.2)).inter
      (((hu.continuous.measurable.comp (hX i)).prodMk
        (hu.continuous.measurable.comp (hY j)))
          (T.core k).window.isCompact_region.measurableSet))

end TaylorTiles
end PopulationLocalPressureCore
end OTSelector.Reconstruction
