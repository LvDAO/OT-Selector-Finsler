import OTSelector.Reconstruction.FinslerOriginalProbePairFunctionalityConcrete
import OTSelector.Reconstruction.FinslerCoefficientPressureFreezing

/-!
# Concrete regularity data for the original tile pair kernel

This module closes the concrete regularity hypotheses of
`FinslerOriginalProbePairFunctionalityConcrete.lean` for the original Finsler
scene tile lane: measurability of the tile cells, pair windows, label and clock
maps and frozen physical cost, measurability and a uniform bound of the concrete
model probe kernel, and a uniform bound on the masked pair cost entry.

## What is proved here

* `measurableSet_tileCell`, `measurableSet_tileWindowRegion`: the tile root cell
  and the rational pair window region are measurable.
* `measurable_u_of_lipschitz`: the original clock map `u` is measurable from its
  one-Lipschitz property (the actual construction supplies exactly this).
* `measurable_frozenPhysicalCost_pair`: the frozen physical cost of a tile, read
  as a function of the pair of sample points, is measurable.
* `exists_frozenCost_bound_on_mask`: on the tile mask the frozen pair cost is
  uniformly bounded, using continuity of the coefficient matrix on the compact
  set `roots x window.region` and the Taylor coordinate diameter of the seed
  label displacement.
* `tileCostPair_abs_le_on_mask`, `tilePairKernel_abs_le_of_masked`: on the mask
  the clipped pair entry is bounded, hence the masked pair kernel is globally
  bounded.
* `tilePairKernel_measurable_of_probe`, `tilePairKernel_bound_of_probe`:
  condition (ii) of the deep tile lane (measurability and uniform bound of the
  masked pair kernel) for every probe family that is pointwise measurable and
  pointwise bounded. Only these two probe-data inputs remain; everything
  geometric is proved here.
* `modelProbeKernel`, `modelProbeKernel_apply_mem`, `modelProbeKernel_abs_le`,
  `measurable_modelProbeKernel`, `modelProbe_tilePairKernel_bound`,
  `modelProbe_tilePairKernel_measurable`: a concrete model probe kernel on
  `M x M`, obtained by extending a bounded continuous probe on the carrier
  `K x K` by zero. It is bounded unconditionally and measurable as soon as the
  carrier probe is measurable; on the carrier it is exactly the given probe.

## Exact remaining sub-gaps

(1) Probe data. The readout theorem consumes `hprobe_meas` (measurability of the
actual scene probe kernel on `M x M`) and a bound on the probe. These are probe
data, not tile geometry: `tilePairKernel_measurable_of_probe` and
`tilePairKernel_bound_of_probe` are proved for an arbitrary probe family once
those two inputs are supplied. For the concrete model probe the bound is proved
unconditionally here; measurability is proved from measurability of the carrier
probe `f : (K x K) ->b R` (`measurable_modelProbeKernel`). A bounded continuous
carrier probe is measurable whenever the product sigma-algebra on `K x K` is the
Borel sigma-algebra, for instance under `[SecondCountableTopology M]`; this
structural instance is not part of the current concrete context (the tile lane
deliberately keeps only `MeasurableSpace`/`BorelSpace` data), which is why it is
recorded as a hypothesis here rather than derived.

(2) Global cost bound. The hypothesis `hcostBound` of
`pressureLower_eq_sceneReadout_of_concreteProbe` asks for a global bound
`forall p : M x M, |tileCostPair ... p| <= B`. That global form is not derivable
and is not what the deep lane consumes: off the window region `tileCostPair`
contains the frozen physical cost, a quadratic form of the inverse interval
integral of the seed label kernel, whose coefficient is unbounded as the clock
separation tends to zero. The deep lane only needs the bound of the multiplied
entry `tilePairKernel` (condition (ii)), which is proved here.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-! ## The concrete model probe kernel on the compact carrier -/

/-- **The concrete model probe kernel.** A bounded continuous probe `f` on the
carrier `K x K` is extended to all pairs `M x M` by zero off the carrier. On the
carrier it is exactly the given probe; off the carrier it is zero. -/
noncomputable def modelProbeKernel {ι : Type*} (K : Set M) (f : (K × K) →ᵇ ℝ)
    (t : ℝ) (n : ℕ) (c : ι) : M × M → ℝ :=
  Function.extend (Subtype.val : ↥(K ×ˢ K) → M × M)
    (fun q : ↥(K ×ˢ K) ↦ f ((MeasurableEquiv.Set.prod K K) q)) (fun _ ↦ 0)

/-- On the carrier the model probe kernel is the original bounded continuous
probe. -/
theorem modelProbeKernel_apply_mem {ι : Type*} {f : (K × K) →ᵇ ℝ} {t : ℝ}
    {n : ℕ} {c : ι} {p : M × M} (hp : p ∈ K ×ˢ K) :
    modelProbeKernel K f t n c p = f ((MeasurableEquiv.Set.prod K K) ⟨p, hp⟩) := by
  show Function.extend (Subtype.val : ↥(K ×ˢ K) → M × M)
    (fun q : ↥(K ×ˢ K) ↦ f ((MeasurableEquiv.Set.prod K K) q)) (fun _ ↦ 0) p = _
  have h := Subtype.val_injective.extend_apply
    (fun q : ↥(K ×ˢ K) ↦ f ((MeasurableEquiv.Set.prod K K) q)) (fun _ ↦ 0)
    ⟨p, hp⟩
  simpa only [show (Subtype.val ⟨p, hp⟩ : M × M) = p from rfl] using h

/-- **The model probe kernel is uniformly bounded** by the sup norm of the
probe. -/
theorem modelProbeKernel_abs_le {ι : Type*} {f : (K × K) →ᵇ ℝ} {t : ℝ} {n : ℕ}
    {c : ι} (p : M × M) :
    |modelProbeKernel K f t n c p| ≤ ‖f‖ := by
  classical
  rw [modelProbeKernel]
  by_cases hp : p ∈ Set.range (Subtype.val : ↥(K ×ˢ K) → M × M)
  · obtain ⟨z, rfl⟩ := hp
    rw [Function.Injective.extend_apply Subtype.val_injective]
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm ((MeasurableEquiv.Set.prod K K) z)
  · rw [Set.mem_range] at hp
    rw [Function.extend_apply' _ _ _ hp, abs_zero]
    exact norm_nonneg _

/-- **Measurability of the model probe kernel** from measurability of the
carrier probe. The extension of a measurable function on `K x K` along the
measurable embedding `Subtype.val` is measurable. -/
theorem measurable_modelProbeKernel {ι : Type*} (hK : MeasurableSet K)
    (f : (K × K) →ᵇ ℝ) (hf : Measurable f) (t : ℝ) (n : ℕ) (c : ι) :
    Measurable (modelProbeKernel K f t n c) := by
  have he : MeasurableEmbedding (Subtype.val : ↥(K ×ˢ K) → M × M) :=
    MeasurableEmbedding.subtype_coe (hK.prod hK)
  have hg : Measurable (fun q : ↥(K ×ˢ K) ↦ f ((MeasurableEquiv.Set.prod K K) q)) :=
    hf.comp (MeasurableEquiv.Set.prod K K).measurable
  show Measurable (Function.extend (Subtype.val : ↥(K ×ˢ K) → M × M)
    (fun q : ↥(K ×ˢ K) ↦ f ((MeasurableEquiv.Set.prod K K) q)) (fun _ ↦ 0))
  exact he.measurable_extend hg measurable_const

/-! ## The frozen pair cost is bounded on the tile mask -/

/-- **The frozen physical cost is uniformly bounded on the tile mask.** The
reference root is a Taylor center and both labels lie in the same partition cell
hence in `roots ∩ neighborhood`, so the Taylor coordinate diameter bounds the
seed label displacement by the Taylor radius; the coefficient matrix is
continuous on the compact set `roots x window.region`, so the quadratic form is
uniformly bounded there. -/
theorem exists_frozenCost_bound_on_mask (c : T.Index) :
    ∃ Mfc : ℝ, 0 ≤ Mfc ∧ ∀ p : M × M, p ∈ T.tileMaskPair c →
      |(T.core c).frozenPhysicalCost (T.reference c) p.1 p.2| ≤ Mfc := by
  classical
  let S := (P (T.core c).seedIndex).seed
  let bW := Module.finBasis ℝ S.covector.ker
  have hA : ContinuousOn (fun z : (ℚ → M) × (ℝ × ℝ) ↦
      populationSeedRootCoefficient S a bW z)
      ((T.core c).roots ×ˢ (T.core c).window.region) :=
    (T.core c).coefficient_continuous
  have hcont : ContinuousOn
      (fun pz : ((ℚ → M) × (ℝ × ℝ)) ×
          (Fin (Module.finrank ℝ S.covector.ker) → ℝ) ↦
        matrixQuadratic (populationSeedRootCoefficient S a bW pz.1) pz.2)
      (((T.core c).roots ×ˢ (T.core c).window.region) ×ˢ
        Metric.closedBall (0 : Fin (Module.finrank ℝ S.covector.ker) → ℝ)
          (T.cover c.1).radius) :=
    continuousOn_matrixQuadratic_field hA _
  have hcompact : IsCompact
      (((T.core c).roots ×ˢ (T.core c).window.region) ×ˢ
        Metric.closedBall (0 : Fin (Module.finrank ℝ S.covector.ker) → ℝ)
          (T.cover c.1).radius) :=
    ((T.core c).roots_compact.prod (T.core c).window.isCompact_region).prod
      (isCompact_closedBall _ _)
  obtain ⟨Cb, hCb⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max Cb 0, le_max_right _ _, ?_⟩
  intro p hp
  simp only [tileMaskPair, Set.mem_ofPred_eq] at hp
  obtain ⟨hp1, hp2, hpreg⟩ := hp
  have hz₀ : T.reference c ∈ (T.cover c.1).centers :=
    (T.partition c.1).center_mem c.2
  have hz₁ : a p.1 ∈ (T.core c).roots ∩ (T.cover c.1).neighborhood (T.reference c) :=
    (T.partition c.1).cell_subset c.2 hp1
  have hz₂ : a p.2 ∈ (T.core c).roots ∩ (T.cover c.1).neighborhood (T.reference c) :=
    (T.partition c.1).cell_subset c.2 hp2
  have hcoord : ‖bW.equivFun (populationSeedRootLabelValue S a (a p.2) -
      populationSeedRootLabelValue S a (a p.1))‖ < (T.cover c.1).radius :=
    (T.cover c.1).coordinate_diameter (T.reference c) hz₀ (a p.1) hz₁ (a p.2) hz₂
  have hv : bW.equivFun (populationSeedRootLabelValue S a (a p.2) -
        populationSeedRootLabelValue S a (a p.1)) ∈
      Metric.closedBall (0 : Fin (Module.finrank ℝ S.covector.ker) → ℝ)
        (T.cover c.1).radius := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hcoord.le
  have hbound := hCb
    ((T.reference c, (u p.1, u p.2)),
      bW.equivFun (populationSeedRootLabelValue S a (a p.2) -
        populationSeedRootLabelValue S a (a p.1)))
    ⟨⟨(T.cover c.1).subset hz₀, hpreg⟩, hv⟩
  have hfrozen : (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2 =
      matrixQuadratic (populationSeedRootCoefficient S a bW
        (T.reference c, (u p.1, u p.2)))
        (bW.equivFun (populationSeedRootLabelValue S a (a p.2) -
          populationSeedRootLabelValue S a (a p.1))) := by
    rw [OriginalPopulationCoefficientCore.frozenPhysicalCost,
      OriginalPopulationCoefficientCore.matrix]
  rw [hfrozen, ← Real.norm_eq_abs]
  exact hbound.trans (le_max_left Cb 0)

/-! ## Bounds on the clipped pair entry -/

/-- **On the mask the clipped pair cost entry is uniformly bounded** from a
bound on the frozen pair cost on the mask and a global bound on the probe. -/
theorem tileCostPair_abs_le_on_mask (c : T.Index) (scale t : ℝ)
    (probeKernel : M × M → ℝ) {Mfc G : ℝ}
    (hfc : ∀ p : M × M, p ∈ T.tileMaskPair c →
      |(T.core c).frozenPhysicalCost (T.reference c) p.1 p.2| ≤ Mfc)
    (hG : ∀ p : M × M, |probeKernel p| ≤ G) :
    ∀ p : M × M, p ∈ T.tileMaskPair c →
      |T.tileCostPair c scale t probeKernel p| ≤
        |1 - 2 * ε| * (|scale| * Mfc) + |t| * G := by
  intro p hp
  have hlin : |(1 - 2 * ε) * (scale * (T.core c).frozenPhysicalCost
        (T.reference c) p.1 p.2) + t * probeKernel p| ≤
      |1 - 2 * ε| * (|scale| * Mfc) + |t| * G := by
    calc
      |(1 - 2 * ε) * (scale * (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2)
          + t * probeKernel p|
          ≤ |(1 - 2 * ε) * (scale * (T.core c).frozenPhysicalCost (T.reference c)
              p.1 p.2)| + |t * probeKernel p| := abs_add_le _ _
      _ = |1 - 2 * ε| * (|scale| *
            |(T.core c).frozenPhysicalCost (T.reference c) p.1 p.2|) +
            |t| * |probeKernel p| := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |1 - 2 * ε| * (|scale| * Mfc) + |t| * G := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hfc p hp) (abs_nonneg scale))
            (abs_nonneg (1 - 2 * ε))
        · exact mul_le_mul_of_nonneg_left (hG p) (abs_nonneg t)
  have hmax : T.tileCostPair c scale t probeKernel p =
      max ((1 - 2 * ε) * (scale * (T.core c).frozenPhysicalCost (T.reference c)
        p.1 p.2) + t * probeKernel p) 0 := rfl
  rw [hmax, abs_of_nonneg (le_max_right _ _)]
  exact (max_le (le_abs_self _) (abs_nonneg _)).trans hlin

/-- **A mask-local bound on the pair cost entry gives a global bound on the
masked pair kernel**: the mask indicator vanishes off the mask. -/
theorem tilePairKernel_abs_le_of_masked (c : T.Index) (scale t : ℝ)
    (probeKernel : M × M → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hcost : ∀ p : M × M, p ∈ T.tileMaskPair c →
      |T.tileCostPair c scale t probeKernel p| ≤ B) :
    ∀ p : M × M, |T.tilePairKernel c scale t probeKernel p| ≤ B := by
  intro p
  show |(T.tileMaskPair c).indicator
    (fun q ↦ T.tileCostPair c scale t probeKernel q) p| ≤ B
  by_cases h : p ∈ T.tileMaskPair c
  · rw [Set.indicator_of_mem h]
    exact hcost p h
  · rw [Set.indicator_of_notMem h, abs_zero]
    exact hB0

/-! ## Measurability of the actual label and clock data -/

/-- The tile root cell is measurable. -/
theorem measurableSet_tileCell (c : T.Index) :
    MeasurableSet ((T.partition c.1).cell c.2) :=
  (T.partition c.1).measurable_cell c.2

/-- The rational pair window region of a tile is measurable (it is compact). -/
theorem measurableSet_tileWindowRegion (c : T.Index) :
    MeasurableSet ((T.core c).window.region) :=
  (T.core c).window.isCompact_region.measurableSet

/-- The original clock map `u` is measurable from its one-Lipschitz property. -/
theorem measurable_u_of_lipschitz
    (hu : let _instTilePairRegularityMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u) :
    Measurable u := by
  let _instTilePairRegularityMetric : MetricSpace M := F.metricSpace
  exact hu.continuous.measurable

/-- The frozen physical cost of a tile, read as a function of the pair of
original sample points, is measurable. -/
theorem measurable_frozenPhysicalCost_pair
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTilePairRegularityMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (c : T.Index) :
    Measurable (fun p : M × M ↦
      (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2) := by
  exact (T.core c).measurable_frozenPhysicalCost hF hcomplete hu ha hinj
    (z := fun _ : M × M ↦ T.reference c) (X := Prod.fst) (Y := Prod.snd)
    measurable_const measurable_fst measurable_snd

/-! ## Condition (ii) of the deep tile lane, proved -/

/-- **Condition (ii), measurability part, for an arbitrary probe family**: the
masked pair kernel of every tile is measurable once the probe family is
pointwise measurable. -/
theorem tilePairKernel_measurable_of_probe
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTilePairRegularityMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (scale : ℕ → ℝ)
    (probeKernel : ((K × K) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobe_meas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (probeKernel f t n c)) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (scale n) t (probeKernel f t n c)) := by
  intro f t n c
  exact measurable_tilePairKernel (T := T) c (scale n) t (probeKernel f t n c)
    (measurableSet_tileCell (T := T) c)
    (measurableSet_tileWindowRegion (T := T) c)
    ha (measurable_u_of_lipschitz hu)
    (measurable_frozenPhysicalCost_pair (T := T) hF hcomplete hu ha hinj c)
    (hprobe_meas f t n c)

/-- **Condition (ii), bound part, for an arbitrary probe family**: the masked
pair kernel of every tile is uniformly bounded once the probe family is
pointwise bounded. The constant is explicit. -/
theorem tilePairKernel_bound_of_probe (scale : ℕ → ℝ)
    (probeKernel : ((K × K) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobe_bd : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ G : ℝ, 0 ≤ G ∧ ∀ p : M × M, |probeKernel f t n c p| ≤ G) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
        |T.tilePairKernel c (scale n) t (probeKernel f t n c) p| ≤ B := by
  intro f t n c
  obtain ⟨Mfc, hMfc0, hMfc⟩ := exists_frozenCost_bound_on_mask (T := T) c
  obtain ⟨G, hG0, hG⟩ := hprobe_bd f t n c
  have hB0 : 0 ≤ |1 - 2 * ε| * (|scale n| * Mfc) + |t| * G := by
    have h1 : 0 ≤ |1 - 2 * ε| * (|scale n| * Mfc) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hMfc0)
    have h2 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg _) hG0
    linarith
  exact ⟨_, hB0, tilePairKernel_abs_le_of_masked (T := T) c (scale n) t
    (probeKernel f t n c) hB0 (fun p hp ↦
      tileCostPair_abs_le_on_mask (T := T) c (scale n) t (probeKernel f t n c)
        hMfc hG p hp)⟩

/-! ## The concrete model probe kernel satisfies the probe data -/

/-- **The masked pair kernel of the model probe is uniformly bounded**,
unconditionally on any geometric or measurability hypothesis. -/
theorem modelProbe_tilePairKernel_bound (scale t : ℝ) (f : (K × K) →ᵇ ℝ)
    (n : ℕ) (c : T.Index) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
      |T.tilePairKernel c scale t (modelProbeKernel K f t n c) p| ≤ B := by
  obtain ⟨Mfc, hMfc0, hMfc⟩ := exists_frozenCost_bound_on_mask (T := T) c
  have hB0 : 0 ≤ |1 - 2 * ε| * (|scale| * Mfc) + |t| * ‖f‖ := by
    have h1 : 0 ≤ |1 - 2 * ε| * (|scale| * Mfc) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hMfc0)
    have h2 : 0 ≤ |t| * ‖f‖ := mul_nonneg (abs_nonneg _) (norm_nonneg f)
    linarith
  exact ⟨_, hB0, tilePairKernel_abs_le_of_masked (T := T) c scale t
    (modelProbeKernel K f t n c) hB0 (fun p hp ↦
      tileCostPair_abs_le_on_mask (T := T) c scale t (modelProbeKernel K f t n c)
        hMfc (fun p ↦ modelProbeKernel_abs_le p) p hp)⟩

/-- **Condition (ii) for the concrete model probe kernel**: for every carrier
probe that is measurable as a function on `K x K` and every tile, the masked
pair kernel of the model probe is measurable. -/
theorem modelProbe_tilePairKernel_measurable
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTilePairRegularityMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hK : MeasurableSet K) (f : (K × K) →ᵇ ℝ) (hf : Measurable f)
    (scale t : ℝ) (n : ℕ) (c : T.Index) :
    Measurable (T.tilePairKernel c scale t (modelProbeKernel K f t n c)) :=
  measurable_tilePairKernel (T := T) c scale t (modelProbeKernel K f t n c)
    (measurableSet_tileCell (T := T) c)
    (measurableSet_tileWindowRegion (T := T) c)
    ha (measurable_u_of_lipschitz hu)
    (measurable_frozenPhysicalCost_pair (T := T) hF hcomplete hu ha hinj c)
    (measurable_modelProbeKernel hK f hf t n c)

/-! ## Assembly of the concrete regularity data -/

/-- **All geometric regularity data of the tile pair lane, assembled**: the tile
cells and pair windows are measurable, the original clock map is measurable, the
frozen physical cost is a measurable pair function, and the frozen pair cost is
uniformly bounded on every tile mask. -/
theorem concrete_tilePairRegularity_data
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTilePairRegularityMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    (∀ c : T.Index, MeasurableSet ((T.partition c.1).cell c.2)) ∧
    (∀ c : T.Index, MeasurableSet ((T.core c).window.region)) ∧
    Measurable u ∧
    (∀ c : T.Index, Measurable (fun p : M × M ↦
      (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2)) ∧
    (∀ c : T.Index, ∃ Mfc : ℝ, 0 ≤ Mfc ∧ ∀ p : M × M, p ∈ T.tileMaskPair c →
      |(T.core c).frozenPhysicalCost (T.reference c) p.1 p.2| ≤ Mfc) :=
  ⟨fun c ↦ measurableSet_tileCell (T := T) c,
    fun c ↦ measurableSet_tileWindowRegion (T := T) c,
    measurable_u_of_lipschitz hu,
    fun c ↦ measurable_frozenPhysicalCost_pair (T := T) hF hcomplete hu ha hinj c,
    fun c ↦ exists_frozenCost_bound_on_mask (T := T) c⟩

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction

