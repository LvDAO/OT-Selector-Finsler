import OTSelector.Reconstruction.RationalScalarPairWindows

/-!
# A countable measurable cover by actual coefficient windows

Each root window retains the same selected seed and the original two conditional
laws. Its measurable tail test makes discarded pair mass uniformly small for all
legal couplings. The original moment and support-gap laws cover almost every root.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- Roots whose original scalar laws fit this rational pair window with the specified loss. -/
def rationalScalarWindowRoots {Z : Type*} [MeasurableSpace Z]
    (μ ν : Kernel Z ℝ) (gap : ℝ) (δ : ℝ≥0∞) (q : RationalScalarPairWindow) : Set Z :=
  scalarSupportInteriorWindow μ ν q.val.1 q.val.2.1 ∩
    {z | (q.val.2.2 : ℝ) ≤ gap ∧ (μ z + ν z) (Icc (q.val.1 : ℝ) q.val.2.1)ᶜ < δ}

/-- The same original conditional kernels give measurable rational-window tests. -/
theorem measurableSet_rationalScalarWindowRoots {Z : Type*} [MeasurableSpace Z]
    (μ ν : Kernel Z ℝ) (gap : ℝ) (δ : ℝ≥0∞) (q : RationalScalarPairWindow) :
    MeasurableSet (rationalScalarWindowRoots μ ν gap δ q) :=
  (measurableSet_scalarSupportInteriorWindow μ ν q.val.1 q.val.2.1).inter
    ((MeasurableSet.const _).inter
      (measurableSet_lt ((μ + ν).measurable_coe measurableSet_Icc.compl) measurable_const))

/-- Every legal coupling of a retained root has the requested small loss on this same region. -/
theorem rationalScalarWindowRoots.uniform_coupling_loss
    {Z : Type*} [MeasurableSpace Z] {μ ν : Kernel Z ℝ} {gap diam : ℝ}
    {δ : ℝ≥0∞} {q : RationalScalarPairWindow} {z : Z}
    (hz : z ∈ rationalScalarWindowRoots μ ν gap δ q)
    (hsep : ConditionalClockSupportBounds (μ z) (ν z) gap diam)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π (μ z) (ν z))
    (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) : π q.regionᶜ < δ := by
  apply (q.measure_compl_region_le hπ ?_).trans_lt hz.2.2
  filter_upwards [hsep.ae_clock_gap_of_coupling hπ horder] with p hp
  exact hz.2.1.trans hp

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [MeasurableSpace Z]

/-- One original seed piece and one rational compact scalar pair window. -/
def populationCoefficientWindowRoots (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (gap : ℝ) (δ : ℝ≥0∞) (i : ℕ × RationalScalarPairWindow) : Set Z :=
  populationSeedRootPiece P a κ lambda i.1 ∩
    rationalScalarWindowRoots (condDistrib u a η₀) (condDistrib u a η₁) gap δ i.2

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]

/-- These actual coefficient windows are measurable in the original root space. -/
theorem measurableSet_populationCoefficientWindowRoots
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCoefficientWindowMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (gap : ℝ) (δ : ℝ≥0∞) (i : ℕ × RationalScalarPairWindow) :
    MeasurableSet (populationCoefficientWindowRoots P a κ lambda η₀ η₁ gap δ i) :=
  (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj i.1).inter
    (measurableSet_rationalScalarWindowRoots _ _ gap δ i.2)

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z] in
/-- The original moment and physical gap laws cover almost every root by the
countable rational windows, for every prescribed positive conditional mass loss. -/
theorem PopulationSeedPieceMomentLaw.ae_mem_coefficientWindowRoots
    (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j)
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∀ᵐ z ∂lambda, z ∈ ⋃ i : ℕ × RationalScalarPairWindow,
      populationCoefficientWindowRoots P a κ lambda η₀ η₁ gap δ i := by
  filter_upwards [hlaw, hcover, hsep] with z hz hzc hs
  obtain ⟨j, hj⟩ := mem_iUnion.mp hzc
  obtain ⟨D⟩ := hz j hj
  obtain ⟨q, hleft, hright, hqgap, hmass, _⟩ := D.exists_rational_pair_window hgap hs hδ
  exact mem_iUnion.mpr ⟨(j, q), hj, ⟨hleft, hright⟩, hqgap, hmass⟩

end OTSelector.Reconstruction
