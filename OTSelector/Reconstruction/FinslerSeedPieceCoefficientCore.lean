import OTSelector.Reconstruction.FinslerSeedRootCoefficientCore
import OTSelector.Reconstruction.FinslerPopulationSeedPieceMoments

/-!
# Actual selected-piece coefficient cores from measurable scalar windows

Positive mass below and above fixed scalar endpoints is a measurable condition
on the two original conditional laws. The actual moment witness then places both
endpoints strictly inside its common support span. This supplies the coefficient
compact-core theorem directly on the original selected seed piece.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- The two original laws place positive mass on both exterior sides of a scalar window. -/
def scalarSupportInteriorWindow {Z : Type*} [MeasurableSpace Z]
    (μ ν : Kernel Z ℝ) (l r : ℝ) : Set Z :=
  {z | 0 < (μ z + ν z) (Iio l) ∧ 0 < (μ z + ν z) (Ioi r)}

/-- Fixed scalar interior screens are measurable without choosing support endpoints. -/
theorem measurableSet_scalarSupportInteriorWindow {Z : Type*} [MeasurableSpace Z]
    (μ ν : Kernel Z ℝ) (l r : ℝ) :
    MeasurableSet (scalarSupportInteriorWindow μ ν l r) := by
  exact (measurableSet_lt measurable_const ((μ + ν).measurable_coe measurableSet_Iio)).inter
    (measurableSet_lt measurable_const ((μ + ν).measurable_coe measurableSet_Ioi))

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- Positive exterior mass places the fixed scalar window inside the same actual support span. -/
theorem OriginalSeedConditionalMoments.scalar_window_mem_support_span
    {S : F.CalibratedLevelSeedPatch u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν) {l r : ℝ} (hlr : l ≤ r)
    (hl : 0 < (μ + ν) (Iio l)) (hr : 0 < (μ + ν) (Ioi r)) :
    l - S.level ∈ Ioo D.lo D.hi ∧ r - S.level ∈ Ioo D.lo D.hi := by
  have hb : ∀ x ∈ (μ + ν).support, x - S.level ∈ Icc D.lo D.hi := by
    intro x hx
    rw [Measure.support_add] at hx
    exact hx.elim (D.support.source.support_bounds x) (D.support.target.support_bounds x)
  obtain ⟨x, hxl, hx⟩ := (μ + ν).nonempty_inter_support_of_pos hl
  obtain ⟨y, hry, hy⟩ := (μ + ν).nonempty_inter_support_of_pos hr
  have hleft : D.lo < l - S.level :=
    (hb x hx).1.trans_lt (sub_lt_sub_right hxl _)
  have hright : r - S.level < D.hi :=
    (sub_lt_sub_right hry _).trans_le (hb y hy).2
  exact ⟨⟨hleft, (sub_le_sub_right hlr _).trans_lt hright⟩,
    ⟨hleft.trans_le (sub_le_sub_right hlr _), hright⟩⟩

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instPieceCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hlaw hF hcomplete hu ha hinj

/-- The same measurable seed piece and exterior-mass screen automatically supply
the original interior scalar-window witness almost everywhere. -/
theorem PopulationSeedPieceMomentLaw.ae_pair_window_on_piece
    (j : ℕ) {l r : ℝ} (hlr : l ≤ r) :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j ∩
      scalarSupportInteriorWindow (condDistrib u a η₀) (condDistrib u a η₁) l r),
      HasOriginalSeedPairWindow (P j).seed a
        (condDistrib u a η₀) (condDistrib u a η₁) l r z := by
  have hs := (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j).inter
    (measurableSet_scalarSupportInteriorWindow (condDistrib u a η₀) (condDistrib u a η₁) l r)
  filter_upwards [ae_restrict_of_ae hlaw, ae_restrict_mem hs] with z hz hzs
  obtain ⟨D⟩ := hz j hzs.1
  exact ⟨populationSeedPieceLabel P a κ lambda j ⟨z, hzs.1⟩,
    populationSeedPieceLabel_root P a κ lambda j ⟨z, hzs.1⟩, D,
    D.scalar_window_mem_support_span hlr hzs.2.1 hzs.2.2⟩

/-- The original physical moment law yields a coefficient continuity core on the
selected piece's measurable interior window, retaining arbitrary original good-label facts. -/
theorem PopulationSeedPieceMomentLaw.exists_coefficient_compact_core
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z] [IsFiniteMeasure lambda]
    (j : ℕ) {l r : ℝ} (hlr : l ≤ r) {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hTsub : T ⊆ {p | p.1 ∈ Icc l r ∧ p.2 ∈ Icc l r ∧ p.1 < p.2})
    {Good : Z → Prop} (hgood : ∀ᵐ z ∂lambda, Good z)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    let s := populationSeedRootPiece P a κ lambda j ∩
      scalarSupportInteriorWindow (condDistrib u a η₀) (condDistrib u a η₁) l r
    ∃ K ⊆ s, IsCompact K ∧ lambda (s \ K) < ε ∧
      ContinuousOn (populationSeedRootCoefficient (P j).seed a
        (Module.finBasis ℝ (P j).seed.covector.ker)) (K ×ˢ T) ∧
      ∀ z ∈ K, HasOriginalSeedPairWindow (P j).seed a
        (condDistrib u a η₀) (condDistrib u a η₁) l r z ∧ Good z := by
  dsimp only
  have hs := (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j).inter
    (measurableSet_scalarSupportInteriorWindow (condDistrib u a η₀) (condDistrib u a η₁) l r)
  have hdata := hlaw.ae_pair_window_on_piece hF hcomplete hu ha hinj j hlr
  have hfull := hdata.and (ae_restrict_of_ae hgood)
  exact exists_populationSeedRootCoefficient_compact_core (P j).seed hF hcomplete hu ha hinj
    hs (measure_ne_top _ _) hlr hT hTsub hfull hε

end OTSelector.Reconstruction
