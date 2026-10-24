import OTSelector.Reconstruction.FinslerPopulationPressureLocalization
import OTSelector.Reconstruction.FinslerTileBlockFrozenComparison
import OTSelector.Geometry.Finsler.SeedKernelMeasurability

/-!
# Probe modulus and far-edge correction for the frozen tile block

`Reconstruction/FinslerTileBlockFrozenComparison.lean` proves the deterministic
per-tile comparison

`physical ≤ (1 + 2 ε) * frozen + min (#S_c) (#T_c) * (|t| * B + 2 ε * |t| * Gb)`,

where `B` is a uniform bound on the probe difference
`|finslerTileProbe - modelProbe|` over the edges of the tile.  This module
supplies the analytic inputs which make that comparison usable at the level of
expectations.

* `uniformProbeModulus` is the oscillation modulus of a bounded continuous
  probe on a compact carrier: `ω 0 = 0`, `ω δ → 0` as `δ → 0`, and
  `|f p - f q| ≤ ω (dist p q)`.
* `abs_finslerTileProbe_sub_modelProbe_le_of_near` turns `ρ`-closeness of the
  physical and model probe readings into the uniform probe bound
  `|finslerTileProbe - modelProbe| ≤ ω ρ`.  The identification of the model
  probe with a reading of the same probe is kept as an explicit structural
  hypothesis, exactly as the atlas/clock lane will supply it.
* `maxCardValue_le_of_le_const_mul_add_edge` and
  `maxCardValue_blockCost_perturbed_le_of_relative_edge` keep the probe error of
  each matched edge separate, replacing the uniform `min (#S_c) (#T_c) * B`
  correction by the sum over one optimal frozen matching.  This is the form
  consumed by the weighted near/far split.
* `integral_normalized_weighted_error_le` and
  `integral_normalized_weighted_probe_error_le` split a fractional probe
  correction into its near part (bounded by the probe modulus) and its far part
  (bounded by the carrier probe norm times the far mass), obtaining the tilted
  bound `|t| * (ω ρ + 2 G * farMass)`.
* `FarGap.expected_original_mass_le_div` restates the geometric far-mass
  estimate, and `tendsto_farMass_of_tendsto_pressure_div_scale` turns it into
  convergence to zero under the explicit asymptotic hypothesis on the
  normalized tilted pressure.
* `probeCorrectionBound` names the resulting additive error, and
  `tendsto_probeCorrectionBound_of_pressure` produces the explicit vanishing
  sequence under `ρ n → 0`, `ε n → 0` and the far-mass estimate.
* `integral_normalized_block_le_model_add` is the resulting additive relaxed
  per-cell comparison: the expected normalized physical block is at most the
  model block sum plus a vanishing additive error.  The law bridge identifying
  the frozen/model expectation with `modelBlockSum` is kept as an explicit
  hypothesis.  `finslerTileBlock_div_le_frozenModelTileBlock_div_add` and
  `finslerNormalizedTileBlock_le_frozenModelTileBlock_add` perform the
  corresponding division of the deterministic Finsler comparison by `n + 1`.

No `sorry`, `admit`, partial definition or added axiom occurs; the only
permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
-/

open Set Function Metric MeasureTheory ProbabilityTheory Filter Manifold Bundle
open scoped Topology ContDiff BigOperators ENNReal BoundedContinuousFunction
open OTSelector.Probability OTSelector.Geometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

/-! ## 1. The uniform probe modulus of a bounded continuous function -/

/-- The set of oscillations `|f p - f q|` of a bounded continuous probe at
distance scale `δ`. -/
def probeOscillationSet {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) (δ : ℝ) : Set ℝ :=
  {r | ∃ p q : α, dist p q ≤ δ ∧ r = |f p - f q|}

/-- The oscillation set is bounded by twice the sup norm of the probe. -/
theorem probeOscillationSet_bddAbove {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) (δ : ℝ) : BddAbove (probeOscillationSet f δ) := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro r ⟨p, q, -, rfl⟩
  rw [← Real.dist_eq]
  exact f.dist_le_two_norm p q

/-- The oscillation set is monotone in the distance scale. -/
theorem probeOscillationSet_mono {α : Type*} [PseudoMetricSpace α]
    {f : α →ᵇ ℝ} {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) :
    probeOscillationSet f δ₁ ⊆ probeOscillationSet f δ₂ := by
  rintro r ⟨p, q, hpq, rfl⟩
  exact ⟨p, q, hpq.trans h, rfl⟩

/-- The union of the oscillation set with `{0}` is bounded above.  The extra
point makes the supremum well defined even for an empty carrier. -/
theorem bddAbove_zero_union_probeOscillationSet {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) (δ : ℝ) : BddAbove ({0} ∪ probeOscillationSet f δ) :=
  bddAbove_singleton.union (probeOscillationSet_bddAbove f δ)

/-- The uniform probe modulus: the supremum of the probe oscillation over
pairs at distance at most `δ`, and `0` for nonpositive `δ`. -/
noncomputable def uniformProbeModulus {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) (δ : ℝ) : ℝ :=
  if δ ≤ 0 then 0 else sSup ({0} ∪ probeOscillationSet f δ)

/-- The modulus vanishes on nonpositive scales, in particular at `0`. -/
theorem uniformProbeModulus_of_nonpos {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) {δ : ℝ} (h : δ ≤ 0) : uniformProbeModulus f δ = 0 := by
  rw [uniformProbeModulus, ite_eq_left h]

/-- The modulus at zero is zero. -/
@[simp] theorem uniformProbeModulus_zero {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) : uniformProbeModulus f 0 = 0 :=
  uniformProbeModulus_of_nonpos f le_rfl

/-- The modulus is nonnegative. -/
theorem uniformProbeModulus_nonneg {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) (δ : ℝ) : 0 ≤ uniformProbeModulus f δ := by
  unfold uniformProbeModulus
  split_ifs with h
  · exact le_rfl
  · exact le_csSup (bddAbove_zero_union_probeOscillationSet f δ) (Or.inl rfl)

/-- The modulus is monotone in the distance scale. -/
theorem uniformProbeModulus_mono {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) :
    uniformProbeModulus f δ₁ ≤ uniformProbeModulus f δ₂ := by
  unfold uniformProbeModulus
  by_cases h₂ : δ₂ ≤ 0
  · rw [ite_eq_left (h.trans h₂), ite_eq_left h₂]
  · rw [ite_eq_right h₂]
    by_cases h₁ : δ₁ ≤ 0
    · rw [ite_eq_left h₁]
      exact le_csSup (bddAbove_zero_union_probeOscillationSet f δ₂) (Or.inl rfl)
    · rw [ite_eq_right h₁]
      apply csSup_le
      · exact ⟨0, Or.inl rfl⟩
      · rintro r (rfl | ⟨p, q, hpq, rfl⟩)
        · exact le_csSup (bddAbove_zero_union_probeOscillationSet f δ₂) (Or.inl rfl)
        · exact le_csSup (bddAbove_zero_union_probeOscillationSet f δ₂)
            (Or.inr ⟨p, q, hpq.trans h, rfl⟩)

/-- The defining property of the uniform probe modulus. -/
theorem abs_probe_sub_le_uniformProbeModulus {α : Type*} [MetricSpace α]
    (f : α →ᵇ ℝ) (p q : α) :
    |f p - f q| ≤ uniformProbeModulus f (dist p q) := by
  rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist p q) with h0 | hpos
  · have hpq : p = q := eq_of_dist_eq_zero h0.symm
    subst hpq
    simp only [sub_self, abs_zero, dist_self, uniformProbeModulus_zero, le_refl]
  · unfold uniformProbeModulus
    rw [ite_eq_right (not_le.mpr hpos)]
    exact le_csSup (bddAbove_zero_union_probeOscillationSet f (dist p q))
      (Or.inr ⟨p, q, le_rfl, rfl⟩)

/-- The modulus bounds the probe difference on pairs at distance at most `ρ`. -/
theorem abs_probe_sub_le_uniformProbeModulus_of_dist_le {α : Type*} [MetricSpace α]
    (f : α →ᵇ ℝ) {p q : α} {ρ : ℝ} (h : dist p q ≤ ρ) :
    |f p - f q| ≤ uniformProbeModulus f ρ :=
  (abs_probe_sub_le_uniformProbeModulus f p q).trans (uniformProbeModulus_mono f h)

/-- The modulus is bounded by twice the sup norm of the probe. -/
theorem uniformProbeModulus_le_two_norm {α : Type*} [PseudoMetricSpace α]
    (f : α →ᵇ ℝ) (δ : ℝ) : uniformProbeModulus f δ ≤ 2 * ‖f‖ := by
  have h2 : 0 ≤ 2 * ‖f‖ := by positivity
  unfold uniformProbeModulus
  split_ifs with h
  · exact h2
  · apply csSup_le
    · exact ⟨0, Or.inl rfl⟩
    · rintro r (rfl | ⟨p, q, -, rfl⟩)
      · exact h2
      · rw [← Real.dist_eq]
        exact f.dist_le_two_norm p q

/-- The Heine--Cantor limit of the uniform probe modulus: uniform continuity of
the probe on the compact carrier makes the oscillation modulus tend to zero. -/
theorem uniformProbeModulus_tendsto_zero {α : Type*} [MetricSpace α] [CompactSpace α]
    (f : α →ᵇ ℝ) :
    Tendsto (uniformProbeModulus f) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  have huc : UniformContinuous (fun x : α => f x) :=
    CompactSpace.uniformContinuous_of_continuous f.continuous
  rw [Metric.uniformContinuous_iff_le] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc (ε / 2) (by linarith)
  refine ⟨δ, hδ0, ?_⟩
  intro x hx
  have hxδ : x < δ := by
    have hx' : |x| < δ := by simpa only [Real.dist_eq, sub_zero] using hx
    exact (abs_lt.mp hx').2
  have hω0 : 0 ≤ uniformProbeModulus f x := uniformProbeModulus_nonneg f x
  have hωε : uniformProbeModulus f x < ε := by
    by_cases hxle : x ≤ 0
    · rw [uniformProbeModulus_of_nonpos f hxle]
      linarith
    · unfold uniformProbeModulus
      rw [ite_eq_right hxle]
      have hsup : sSup ({0} ∪ probeOscillationSet f x) ≤ ε / 2 := by
        apply csSup_le
        · exact ⟨0, Or.inl rfl⟩
        · rintro r (rfl | ⟨p, q, hpq, rfl⟩)
          · linarith
          · have hpq' : dist p q ≤ δ := hpq.trans (le_of_lt hxδ)
            have hle := hδ hpq'
            rwa [Real.dist_eq] at hle
      linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hω0]
  exact hωε

/-- **Uniform probe modulus on a compact metric carrier.**  For a bounded
continuous real probe on a compact metric space there is a modulus `ω` with
`ω 0 = 0`, `Tendsto ω (𝓝 0) (𝓝 0)`, nonnegative values, and
`|f p - f q| ≤ ω (dist p q)`. -/
theorem exists_uniform_probe_modulus {α : Type*} [MetricSpace α] [CompactSpace α]
    (f : α →ᵇ ℝ) :
    ∃ w : ℝ → ℝ, w 0 = 0 ∧ Tendsto w (𝓝 0) (𝓝 0) ∧
      (∀ δ, 0 ≤ w δ) ∧ ∀ p q : α, |f p - f q| ≤ w (dist p q) :=
  ⟨uniformProbeModulus f, uniformProbeModulus_zero f,
    uniformProbeModulus_tendsto_zero f, uniformProbeModulus_nonneg f,
    abs_probe_sub_le_uniformProbeModulus f⟩

/-- **Uniform probe modulus on a compact carrier `K ⊆ M`.**  The probe is a
bounded continuous function on `K × K`, and the modulus is taken in the
product metric on the carrier. -/
theorem exists_uniform_probe_modulus_compactCarrier {M : Type*} [MetricSpace M]
    {K : Set M} (hK : IsCompact K) (f : (K × K) →ᵇ ℝ) :
    ∃ w : ℝ → ℝ, w 0 = 0 ∧ Tendsto w (𝓝 0) (𝓝 0) ∧
      (∀ δ, 0 ≤ w δ) ∧ ∀ p q : K × K, |f p - f q| ≤ w (dist p q) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompactSpace (K × K) := inferInstance
  exact exists_uniform_probe_modulus f

/-! ## 2. Near-pair probe comparison

The physical probe is `f` evaluated at the two carrier points.  The model probe
is `f` evaluated at model readings of the same two labels.  Uniform continuity
of `f` turns closeness of the readings into a bound `ω ρ` on the probe
difference.  The identification of the model probe with such a reading is a
structural atlas hypothesis; it is the only unproved geometric input here. -/

/-- The product-distance form of the modulus bound. -/
theorem abs_probe_sub_le_of_near_coordinates {K : Type*} [MetricSpace K]
    (f : (K × K) →ᵇ ℝ) {x₁ x₂ y₁ y₂ : K} {ρ : ℝ}
    (hx : dist x₁ x₂ ≤ ρ) (hy : dist y₁ y₂ ≤ ρ) :
    |f (x₁, y₁) - f (x₂, y₂)| ≤ uniformProbeModulus f ρ := by
  apply abs_probe_sub_le_uniformProbeModulus_of_dist_le
  rw [Prod.dist_eq]
  exact max_le hx hy

/-- The one-coordinate (mark-only) form: only the target reading moves. -/
theorem abs_probe_sub_snd_le_of_near_coordinates {K : Type*} [MetricSpace K]
    (f : (K × K) →ᵇ ℝ) {x y₁ y₂ : K} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hy : dist y₁ y₂ ≤ ρ) :
    |f (x, y₁) - f (x, y₂)| ≤ uniformProbeModulus f ρ :=
  abs_probe_sub_le_of_near_coordinates f (by simpa using hρ) hy

/-- The source-coordinate (mark-only) form. -/
theorem abs_probe_sub_fst_le_of_near_coordinates {K : Type*} [MetricSpace K]
    (f : (K × K) →ᵇ ℝ) {x₁ x₂ y : K} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hx : dist x₁ x₂ ≤ ρ) :
    |f (x₁, y) - f (x₂, y)| ≤ uniformProbeModulus f ρ :=
  abs_probe_sub_le_of_near_coordinates f hx (by simpa using hρ)




/-! ## 2. The near-pair probe comparison in the Finsler tile

The physical probe `finslerTileProbe` evaluates the bounded continuous probe at
the support projections of the two sample points.  The model probe evaluates
the same probe at model readings of the two labels.  If both readings are close
to the physical projections, uniform continuity of the probe bounds the probe
difference by the modulus `ω ρ`.  The existence of such model readings with the
required closeness is the atlas/clock input; it is kept explicit. -/

section FinslerProbe

variable {M : Type*} [MetricSpace M] [MeasurableSpace M]

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- **Near-pair probe comparison.**  If the source and target physical carrier
points are within `ρ` of the model readings, and the model probe is the same
bounded continuous probe evaluated at those readings, then the probe difference
on the edge is at most `uniformProbeModulus f ρ`. -/
theorem abs_finslerTileProbe_sub_modelProbe_le_of_near
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (X Y : Fin (n + 1) → M) (f : (K × K) →ᵇ ℝ)
    (modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ)
    (modelS modelT : Fin (n + 1) → Fin (n + 1) → K) {ρ : ℝ}
    (hmodel : ∀ i j, modelProbe i j = f (modelS i j, modelT i j))
    (hS : ∀ i j, dist (supportProjection μ K hK hμ (X i)) (modelS i j) ≤ ρ)
    (hT : ∀ i j, dist (supportProjection ν K hK hν (Y j)) (modelT i j) ≤ ρ) :
    ∀ i j, |finslerTileProbe μ ν K hK hμ hν X Y f i j - modelProbe i j| ≤
      uniformProbeModulus f ρ := by
  intro i j
  have hd : dist (((supportProjection μ K hK hμ (X i),
      supportProjection ν K hK hν (Y j)) : K × K)) (modelS i j, modelT i j) ≤ ρ := by
    rw [Prod.dist_eq]
    exact max_le (hS i j) (hT i j)
  have h := abs_probe_sub_le_uniformProbeModulus f
    ((supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j)) : K × K)
    (modelS i j, modelT i j)
  rw [finslerTileProbe, hmodel]
  exact h.trans (uniformProbeModulus_mono f hd)

/-- The tile-restricted form consumed by `finslerTileBlock_le_frozenModelTileBlock`:
only the edges of tile `c` need the near-reading hypothesis. -/
theorem finslerTileProbe_modelProbe_bound_on_tile
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (X Y : Fin (n + 1) → M) (f : (K × K) →ᵇ ℝ)
    (blockS blockT : Fin (n + 1) → ι) (c : ι)
    (modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ)
    (modelS modelT : Fin (n + 1) → Fin (n + 1) → K) {ρ : ℝ}
    (hmodel : ∀ i j, modelProbe i j = f (modelS i j, modelT i j))
    (hS : ∀ i j, blockS i = c → blockT j = c →
      dist (supportProjection μ K hK hμ (X i)) (modelS i j) ≤ ρ)
    (hT : ∀ i j, blockS i = c → blockT j = c →
      dist (supportProjection ν K hK hν (Y j)) (modelT i j) ≤ ρ) :
    ∀ i j, blockS i = c → blockT j = c →
      |finslerTileProbe μ ν K hK hμ hν X Y f i j - modelProbe i j| ≤
        uniformProbeModulus f ρ := by
  intro i j hi hj
  have hd : dist (((supportProjection μ K hK hμ (X i),
      supportProjection ν K hK hν (Y j)) : K × K)) (modelS i j, modelT i j) ≤ ρ := by
    rw [Prod.dist_eq]
    exact max_le (hS i j hi hj) (hT i j hi hj)
  have h := abs_probe_sub_le_uniformProbeModulus f
    ((supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j)) : K × K)
    (modelS i j, modelT i j)
  rw [finslerTileProbe, hmodel]
  exact h.trans (uniformProbeModulus_mono f hd)

end FinslerProbe

/-! ## 2b. Extracting the label closeness from the far/near localization

The actual near-pair relation of `FinslerDistanceLocalizationPhysical` contains
the concrete label estimate which the atlas/clock reading input consumes. -/

section NearLabelExtraction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}

/-- Membership in `nearPhysicalPairs` exposes one retained core piece, both
physical endpoints in it, and the actual seed labels within `radius`. -/
theorem nearPhysicalPairs_exists_label_close
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    {radius : ℝ} {p : M × M} (hp : p ∈ D.nearPhysicalPairs radius) :
    ∃ i : Fin D.haar.continuous.count,
      p.1 ∈ D.physicalCoreDomain i ∧ p.2 ∈ D.physicalCoreDomain i ∧
      ‖populationSeedRootLabelValue
          (P (D.haar.continuous.coefficient i).seedIndex).seed a (a p.2) -
        populationSeedRootLabelValue
          (P (D.haar.continuous.coefficient i).seedIndex).seed a (a p.1)‖ < radius := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  exact ⟨i, hi.1.1, hi.1.2, hi.2⟩

/-- The far-pair set is the complement of the near-pair set inside the retained
physical core. -/
theorem farPhysicalPairs_eq_sdiff_near
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (radius : ℝ) :
    D.farPhysicalPairs radius =
      ((⋃ i, D.physicalCoreDomain i) ×ˢ (⋃ i, D.physicalCoreDomain i)) \
        D.nearPhysicalPairs radius := rfl

end NearLabelExtraction


/-! ## 3. The far-edge mass estimate and its vanishing form

`FarGap.expected_original_mass` bounds the expected normalized mass of the far
edges of any measurable fractional optimizer by the tilted pressure divided by
`scale * gap`.  We restate the inequality in this module and record the scalar
squeeze which turns it into convergence to zero. -/

section FarEdgeMass

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}

namespace PopulationLocalPressureCore

/-- **Far-edge mass bound.**  For every measurable fractional optimizer of the
tilted original pressure, the expected normalized mass of edges whose original
physical pair is far (label distance at least `radius`) is at most the expected
normalized tilted pressure plus the tilted probe bound, divided by
`scale * gap`. -/
theorem FarGap.expected_original_mass_le_div
    {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε}
    {radius : ℝ} (G : D.FarGap radius)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFarMassMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} [IsProbabilityMeasure sample]
    {n : ℕ} (hn : 0 < n) (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    (hXlaw : ∀ i, sample.map (fun ξ ↦ X ξ i) = η₀)
    (hYlaw : ∀ j, sample.map (fun ξ ↦ Y ξ j) = η₁)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ y ∂η₁, y ∈ B)
    (g W : Ω → Matrix (Fin n) (Fin n) ℝ) (t probeBound scale : ℝ)
    (hscale : 0 < scale)
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hW : ∀ i j, Measurable (fun ξ ↦ W ξ i j))
    (hgb : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ probeBound)
    (hopt : ∀ᵐ ξ ∂sample, OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j ↦ scale *
        ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i))) (g ξ) t) (W ξ)) :
    let c := fun ξ i j ↦ scale *
      ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i))
    let Q := fun ξ ↦ {ij | (X ξ ij.1, Y ξ ij.2) ∈ D.farPhysicalPairs radius}
    Integrable (fun ξ ↦ fractionalEdgeMass (Q ξ) (W ξ)) sample ∧
      (∫ ξ, fractionalEdgeMass (Q ξ) (W ξ) ∂sample) ≤
        ((∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / n ∂sample) +
          |t| * probeBound) / (scale * G.value) :=
  FarGap.expected_original_mass D G hF hcomplete hu ha hinj hn X Y hX hY hXlaw hYlaw
    hA hB hη₀A hη₁B g W t probeBound scale hscale hg hW hgb hopt

end PopulationLocalPressureCore

/-- **Scalar squeeze for the far mass.**  A nonnegative sequence bounded by
`A n / (s n * gap)`, whose normalized numerator `A n / s n` tends to zero,
tends to zero. -/
theorem tendsto_of_nonneg_le_div_mul_of_tendsto_div
    {mass numerator scale : ℕ → ℝ} {gap : ℝ}
    (hmass : ∀ n, 0 ≤ mass n)
    (hle : ∀ n, mass n ≤ numerator n / (scale n * gap))
    (_hgap : 0 < gap)
    (hnum : Tendsto (fun n => numerator n / scale n) atTop (𝓝 0)) :
    Tendsto mass atTop (𝓝 0) := by
  have hbound : Tendsto (fun n => numerator n / (scale n * gap)) atTop (𝓝 0) := by
    simpa only [div_div, zero_div] using hnum.div_const gap
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun n => hmass n) (fun n => hle n)

/-- **Far mass vanishes when the normalized tilted pressure does.**  If the
expected tilted pressure divided by the kinetic scale tends to zero and the
geometric far gap stays away from zero, then the expected normalized far mass
tends to zero. -/
theorem tendsto_farMass_of_tendsto_pressure_div_scale
    {mass pressure probeBound scale : ℕ → ℝ} {t gap : ℝ}
    (hmass : ∀ n, 0 ≤ mass n)
    (hle : ∀ n, mass n ≤ (pressure n + |t| * probeBound n) / (scale n * gap))
    (hgap : 0 < gap)
    (hpressure : Tendsto (fun n => (pressure n + |t| * probeBound n) / scale n)
      atTop (𝓝 0)) :
    Tendsto mass atTop (𝓝 0) :=
  tendsto_of_nonneg_le_div_mul_of_tendsto_div hmass hle hgap hpressure

/-- **Far mass vanishes as the kinetic scale grows.**  If the numerator of the
pressure estimate is bounded by a constant `C` and the kinetic scale tends to
infinity while the far gap is bounded below, the far-mass bound tends to zero.
This is the scalar form used when the tilted pressure is first normalized by
the kinetic scale. -/
theorem tendsto_const_div_mul_of_tendsto_atTop
    {C gap : ℝ} {scale : ℕ → ℝ}
    (hgap : 0 < gap) (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n => C / (scale n * gap)) atTop (𝓝 0) :=
  (hscale.atTop_mul_const hgap).const_div_atTop C

end FarEdgeMass

/-! ## 4. The weighted probe correction: near plus far

For a fractional coupling `W`, the normalized tilted probe correction is the
`W`-weighted average of the per-edge probe errors.  Near edges contribute at
most the probe modulus and far edges at most twice the probe sup norm times the
far mass. -/

section WeightedProbeCorrection

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ}

/-- The edge mass of a subset of a nonnegative matrix is at most its total
mass. -/
theorem sum_filter_le_sum_of_nonneg (W : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n × Fin n → Prop) [DecidablePred q]
    (hW : ∀ i j, 0 ≤ W i j) :
    (∑ i, ∑ j, if q (i, j) then W i j else 0) ≤ ∑ i, ∑ j, W i j := by
  classical
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with h
  · exact le_rfl
  · exact hW i j

/-- **Pointwise near/far split.**  If `err` is at most `b` off the far set and
at most `2 G` everywhere, and `W` is nonnegative with total mass at most `n`,
then the normalized `W`-weighted error is at most `b + 2 G * farMass`. -/
theorem normalized_weighted_error_le_near_add_far
    (hn : 0 < n) {W err : Matrix (Fin n) (Fin n) ℝ}
    {far : Set (Fin n × Fin n)} {b G : ℝ}
    (hb : 0 ≤ b)
    (hW : ∀ i j, 0 ≤ W i j)
    (hWmass : ∑ i, ∑ j, W i j ≤ (n : ℝ))
    (hnear : ∀ i j, (i, j) ∉ far → err i j ≤ b)
    (hfar : ∀ i j, err i j ≤ 2 * G) :
    (1 / (n : ℝ)) * ∑ i, ∑ j, W i j * err i j ≤
      b + 2 * G * fractionalEdgeMass far W := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnear_sum : (∑ i, ∑ j, if (i, j) ∉ far then W i j else 0) ≤ (n : ℝ) :=
    (sum_filter_le_sum_of_nonneg W (fun p => p ∉ far) hW).trans hWmass
  have hsplit : (∑ i, ∑ j, W i j * err i j) =
      (∑ i, ∑ j, if (i, j) ∈ far then W i j * err i j else 0) +
      (∑ i, ∑ j, if (i, j) ∉ far then W i j * err i j else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : (i, j) ∈ far <;> simp [h]
  have hfar_part :
      (∑ i, ∑ j, if (i, j) ∈ far then W i j * err i j else 0) ≤
        2 * G * (∑ i, ∑ j, if (i, j) ∈ far then W i j else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : (i, j) ∈ far
    · simp only [h, ite_true]
      calc W i j * err i j ≤ W i j * (2 * G) :=
            mul_le_mul_of_nonneg_left (hfar i j) (hW i j)
        _ = 2 * G * W i j := by ring
    · simp [h]
  have hnear_part :
      (∑ i, ∑ j, if (i, j) ∉ far then W i j * err i j else 0) ≤ b * (n : ℝ) := by
    have h1 : (∑ i, ∑ j, if (i, j) ∉ far then W i j * err i j else 0) ≤
        ∑ i, ∑ j, if (i, j) ∉ far then W i j * b else 0 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases h : (i, j) ∉ far
      · simp only [h]
        exact mul_le_mul_of_nonneg_left (hnear i j h) (hW i j)
      · simp [h]
    have h2 : (∑ i, ∑ j, if (i, j) ∉ far then W i j * b else 0) =
        b * (∑ i, ∑ j, if (i, j) ∉ far then W i j else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : (i, j) ∉ far <;> simp [h, mul_comm]
    calc
      _ ≤ ∑ i, ∑ j, if (i, j) ∉ far then W i j * b else 0 := h1
      _ = b * (∑ i, ∑ j, if (i, j) ∉ far then W i j else 0) := h2
      _ ≤ b * (n : ℝ) := mul_le_mul_of_nonneg_left hnear_sum hb
  rw [hsplit]
  have hmain : (∑ i, ∑ j, if (i, j) ∈ far then W i j * err i j else 0) +
      (∑ i, ∑ j, if (i, j) ∉ far then W i j * err i j else 0) ≤
      2 * G * (∑ i, ∑ j, if (i, j) ∈ far then W i j else 0) + b * (n : ℝ) :=
    add_le_add hfar_part hnear_part
  have hdiv := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  have hrm : fractionalEdgeMass far W =
      (∑ i, ∑ j, if (i, j) ∈ far then W i j else 0) / (n : ℝ) := by
    simp only [fractionalEdgeMass]
  rw [hrm]
  have hrewrite : (1 / (n : ℝ)) *
      (2 * G * (∑ i, ∑ j, if (i, j) ∈ far then W i j else 0) + b * (n : ℝ)) =
      b + 2 * G * ((∑ i, ∑ j, if (i, j) ∈ far then W i j else 0) / (n : ℝ)) := by
    field_simp
    ring
  rw [← hrewrite]
  exact hdiv

/-- **Expected weighted probe correction.**  The expectation of the normalized
`W`-weighted error is at most `b + 2 G * M`, where `M` bounds the expected far
mass. -/
theorem integral_normalized_weighted_error_le
    (hn : 0 < n)
    (W err : Ω → Matrix (Fin n) (Fin n) ℝ)
    (far : Ω → Set (Fin n × Fin n))
    {b G M : ℝ} (hb : 0 ≤ b) (hG : 0 ≤ G)
    (hWnonneg : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ W ξ i j)
    (hWmass : ∀ᵐ ξ ∂P, ∑ i, ∑ j, W ξ i j ≤ (n : ℝ))
    (hnear : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∉ far ξ → err ξ i j ≤ b)
    (hfar_bound : ∀ᵐ ξ ∂P, ∀ i j, err ξ i j ≤ 2 * G)
    (hint : Integrable (fun ξ => (1 / (n : ℝ)) * ∑ i, ∑ j, W ξ i j * err ξ i j) P)
    (hfar_int : Integrable (fun ξ => fractionalEdgeMass (far ξ) (W ξ)) P)
    (hfar : ∫ ξ, fractionalEdgeMass (far ξ) (W ξ) ∂P ≤ M) :
    (∫ ξ, (1 / (n : ℝ)) * ∑ i, ∑ j, W ξ i j * err ξ i j ∂P) ≤
      b + 2 * G * M := by
  have hbound_int : Integrable (fun ξ => b + 2 * G * fractionalEdgeMass (far ξ) (W ξ)) P :=
    (integrable_const b).add (hfar_int.const_mul (2 * G))
  have hle := integral_mono_ae hint hbound_int (by
    filter_upwards [hWnonneg, hWmass, hnear, hfar_bound] with ξ hWn hWm hn1 hf1
    exact normalized_weighted_error_le_near_add_far hn hb hWn hWm hn1 hf1)
  calc
    (∫ ξ, (1 / (n : ℝ)) * ∑ i, ∑ j, W ξ i j * err ξ i j ∂P)
        ≤ ∫ ξ, (b + 2 * G * fractionalEdgeMass (far ξ) (W ξ)) ∂P := hle
    _ = b + 2 * G * ∫ ξ, fractionalEdgeMass (far ξ) (W ξ) ∂P := by
        rw [integral_add (integrable_const b) (hfar_int.const_mul (2 * G)),
          integral_const_mul, integral_const]
        simp
    _ ≤ b + 2 * G * M :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hfar (by linarith))


/-- **Expected tilted probe correction.**  With the per-edge error
`|t| * |probeErr|`, the normalized expected correction is at most
`|t| * (ω ρ + 2 G M)`, where `M` bounds the expected far mass. -/
theorem integral_normalized_weighted_probe_error_le
    (hn : 0 < n)
    (W probeErr : Ω → Matrix (Fin n) (Fin n) ℝ)
    (far : Ω → Set (Fin n × Fin n))
    {t ωρ G M : ℝ} (hωρ : 0 ≤ ωρ) (hG : 0 ≤ G)
    (hWnonneg : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ W ξ i j)
    (hWmass : ∀ᵐ ξ ∂P, ∑ i, ∑ j, W ξ i j ≤ (n : ℝ))
    (hnear : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∉ far ξ → |probeErr ξ i j| ≤ ωρ)
    (hglobal : ∀ᵐ ξ ∂P, ∀ i j, |probeErr ξ i j| ≤ 2 * G)
    (hint : Integrable (fun ξ =>
      (1 / (n : ℝ)) * ∑ i, ∑ j, W ξ i j * (|t| * |probeErr ξ i j|)) P)
    (hfar_int : Integrable (fun ξ => fractionalEdgeMass (far ξ) (W ξ)) P)
    (hfar : ∫ ξ, fractionalEdgeMass (far ξ) (W ξ) ∂P ≤ M) :
    (∫ ξ, (1 / (n : ℝ)) * ∑ i, ∑ j, W ξ i j * (|t| * |probeErr ξ i j|) ∂P) ≤
      |t| * (ωρ + 2 * G * M) := by
  have h := integral_normalized_weighted_error_le (n := n) hn W
    (fun ξ i j => |t| * |probeErr ξ i j|) far
    (b := |t| * ωρ) (G := |t| * G) (M := M)
    (mul_nonneg (abs_nonneg t) hωρ) (mul_nonneg (abs_nonneg t) hG)
    hWnonneg hWmass ?_ ?_ hint hfar_int hfar
  · calc
      (∫ ξ, (1 / (n : ℝ)) *
          ∑ i, ∑ j, W ξ i j * (|t| * |probeErr ξ i j|) ∂P)
          ≤ |t| * ωρ + 2 * (|t| * G) * M := h
      _ = |t| * (ωρ + 2 * G * M) := by ring
  · filter_upwards [hnear] with ξ hξ i j hij
    exact mul_le_mul_of_nonneg_left (hξ i j hij) (abs_nonneg t)
  · filter_upwards [hglobal] with ξ hξ i j
    calc |t| * |probeErr ξ i j| ≤ |t| * (2 * G) :=
          mul_le_mul_of_nonneg_left (hξ i j) (abs_nonneg t)
      _ = 2 * (|t| * G) := by ring

end WeightedProbeCorrection


/-! ## 4c. Per-edge maximum-cardinality stability

The frozen comparison of `FinslerTileBlockFrozenComparison` uses a uniform
probe bound `B` and therefore a correction `min (#S_c) (#T_c) * B`.  For the
expectation split it is better to keep the probe error of each matched edge.
The next two lemmas are the per-edge version: the correction becomes the sum of
the per-edge errors over one optimal frozen matching, which is exactly a
weighted sum to which `integral_normalized_weighted_error_le` applies. -/

section PerEdgeMaxCard

open OTSelector.PartialMatching

/-- **Per-edge affine comparison for `maxCardValue`.**  If `c ≤ α d + B`
entrywise, then the value of `c` is at most `α` times the value of `d` plus the
sum of `B` over the edges of any optimal maximum-cardinality matching of `d`. -/
theorem maxCardValue_le_of_le_const_mul_add_edge {a b : ℕ}
    {c d B : Fin a → Fin b → ℝ} {α : ℝ}
    {σ : PartialMatching a b}
    (hσ : σ.card = min a b)
    (hσd : σ.cost d = maxCardValue d)
    (h : ∀ i j, c i j ≤ α * d i j + B i j) :
    maxCardValue c ≤ α * maxCardValue d + ∑ e ∈ σ.edges, B e.1 e.2 := by
  classical
  have h1 : maxCardValue c ≤ σ.cost c := maxCardValue_le_of_card c hσ
  have h2 : σ.cost c ≤ σ.cost (fun i j => α * d i j + B i j) := by
    unfold cost
    exact Finset.sum_le_sum fun e _ => h e.1 e.2
  have hsplit : σ.cost (fun i j => α * d i j + B i j) =
      α * σ.cost d + ∑ e ∈ σ.edges, B e.1 e.2 := by
    unfold cost
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, hσd] at h2
  exact h1.trans h2

/-- **Per-edge frozen-block comparison.**  The probe error on each matched edge
is kept separate.  If the frozen matching `σ` attains the frozen block value,
the physical block is at most `(1 + δ)` times the frozen block plus the sum of
`|t| * B` and the relative-kinetic correction `δ * |t| * Gb` over the edges of
`σ`. -/
theorem maxCardValue_blockCost_perturbed_le_of_relative_edge
    {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (blockS : Fin N → β) (blockT : Fin N → β) (c : β)
    {P F G Q : Fin N → Fin N → ℝ} {t δ Gb : ℝ}
    {B : Fin (blockSizeS blockS c) → Fin (blockSizeT blockT c) → ℝ}
    {σ : PartialMatching (blockSizeS blockS c) (blockSizeT blockT c)}
    (hσ : σ.card = min (blockSizeS blockS c) (blockSizeT blockT c))
    (hσd : σ.cost (blockCost blockS blockT (perturbedEdgeCost F G t) c) =
      maxCardValue (blockCost blockS blockT (perturbedEdgeCost F G t) c))
    (hδ0 : 0 ≤ δ)
    (hF0 : ∀ i j, blockS i = c → blockT j = c → 0 ≤ F i j)
    (hrel : ∀ i j, blockS i = c → blockT j = c → |P i j - F i j| ≤ δ * F i j)
    (hprobe : ∀ i j,
      |Q (blockEmbeddingS blockS c i) (blockEmbeddingT blockT c j) -
        G (blockEmbeddingS blockS c i) (blockEmbeddingT blockT c j)| ≤ B i j)
    (hG : ∀ i j, blockS i = c → blockT j = c → |G i j| ≤ Gb) :
    maxCardValue (blockCost blockS blockT (perturbedEdgeCost P Q t) c) ≤
      (1 + δ) * maxCardValue (blockCost blockS blockT (perturbedEdgeCost F G t) c) +
        ∑ e ∈ σ.edges, (|t| * B e.1 e.2 + δ * (|t| * Gb)) := by
  classical
  have hS : ∀ i, blockS (blockEmbeddingS blockS c i) = c := fun i =>
    mem_blockFinset.mp (blockEmbeddingS_mem blockS c i)
  have hT : ∀ j, blockT (blockEmbeddingT blockT c j) = c := fun j =>
    mem_blockFinset.mp (blockEmbeddingT_mem blockT c j)
  refine maxCardValue_le_of_le_const_mul_add_edge
    (c := blockCost blockS blockT (perturbedEdgeCost P Q t) c)
    (d := blockCost blockS blockT (perturbedEdgeCost F G t) c)
    (B := fun e1 e2 => |t| * B e1 e2 + δ * (|t| * Gb))
    (α := 1 + δ) (σ := σ) hσ hσd ?_
  intro i j
  rw [blockCost_perturbedEdgeCost blockS blockT c P Q t,
    blockCost_perturbedEdgeCost blockS blockT c F G t]
  have h1 : blockCost blockS blockT P c i j - blockCost blockS blockT F c i j ≤
      δ * blockCost blockS blockT F c i j :=
    (abs_le.mp (hrel _ _ (hS i) (hT j))).2
  have h2 : t * (blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j) ≤
      |t| * B i j := by
    have hp := hprobe i j
    calc t * (blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j)
        ≤ |t * (blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j)| :=
          le_abs_self _
      _ = |t| * |blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j| :=
          abs_mul _ _
      _ ≤ |t| * B i j := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
          simpa only [blockCost] using hp
  have h3 : -(|t| * Gb) ≤ t * blockCost blockS blockT G c i j := by
    have h4 : |t * blockCost blockS blockT G c i j| ≤ |t| * Gb := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hG _ _ (hS i) (hT j)) (abs_nonneg t)
    linarith [neg_abs_le (t * blockCost blockS blockT G c i j)]
  have h5 : δ * (-(|t| * Gb)) ≤ δ * (t * blockCost blockS blockT G c i j) :=
    mul_le_mul_of_nonneg_left h3 hδ0
  have hF := hF0 _ _ (hS i) (hT j)
  nlinarith [h1, h2, h5, hF]

end PerEdgeMaxCard

/-! ## 4b. The explicit correction bound and its vanishing sequence -/

/-- The additive correction of the frozen-block comparison: the tilted near
probe error `|t| * ω ρ`, the tilted far contribution `|t| * 2 G * farMass`, and
the relative-kinetic correction `2 ε |t| Gb`. -/
noncomputable def probeCorrectionBound (t G Gb : ℝ) (modulus : ℝ → ℝ)
    (ρ farMass ε : ℝ) : ℝ :=
  |t| * (modulus ρ + 2 * G * farMass) + 2 * ε * |t| * Gb

/-- The correction bound is nonnegative under the natural sign hypotheses. -/
theorem probeCorrectionBound_nonneg {t G Gb : ℝ} {modulus : ℝ → ℝ} {ρ farMass ε : ℝ}
    (hω : 0 ≤ modulus ρ) (hG : 0 ≤ G) (hfarMass : 0 ≤ farMass)
    (hε : 0 ≤ ε) (hGb : 0 ≤ Gb) :
    0 ≤ probeCorrectionBound t G Gb modulus ρ farMass ε := by
  unfold probeCorrectionBound
  have h1 : 0 ≤ modulus ρ + 2 * G * farMass := by positivity
  have h2 : 0 ≤ 2 * ε * |t| * Gb := by positivity
  exact add_nonneg (mul_nonneg (abs_nonneg t) h1) h2

/-- **Vanishing of the correction.**  If the probe modulus vanishes at zero,
the near-label radius and the expected far mass tend to zero, and the relative
kinetic error tends to zero, then the explicit correction bound tends to zero. -/
theorem tendsto_probeCorrectionBound_zero {t G Gb : ℝ} {modulus : ℝ → ℝ}
    {ρ farMass ε : ℕ → ℝ}
    (hω : Tendsto modulus (𝓝 0) (𝓝 0))
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hfarMass : Tendsto farMass atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => probeCorrectionBound t G Gb modulus (ρ n) (farMass n) (ε n))
      atTop (𝓝 0) := by
  unfold probeCorrectionBound
  have h1 : Tendsto (fun n => modulus (ρ n)) atTop (𝓝 0) := hω.comp hρ
  have h2 : Tendsto (fun n => 2 * G * farMass n) atTop (𝓝 (2 * G * 0)) :=
    tendsto_const_nhds.mul hfarMass
  have h3 : Tendsto (fun n => modulus (ρ n) + 2 * G * farMass n) atTop
      (𝓝 (0 + 2 * G * 0)) := h1.add h2
  have h4 : Tendsto (fun n => |t| * (modulus (ρ n) + 2 * G * farMass n)) atTop
      (𝓝 (|t| * (0 + 2 * G * 0))) := tendsto_const_nhds.mul h3
  have h5 : Tendsto (fun n => 2 * ε n * |t| * Gb) atTop (𝓝 (2 * 0 * |t| * Gb)) := by
    have hε2 : Tendsto (fun n => 2 * ε n) atTop (𝓝 (2 * 0)) :=
      tendsto_const_nhds.mul hε
    exact (hε2.mul tendsto_const_nhds).mul tendsto_const_nhds
  simpa using h4.add h5

/-- **Explicit vanishing correction sequence.**  Choose a near-label radius
`ρ n → 0`, a relative kinetic error `ε n → 0`, and define the far-mass sequence
by the geometric estimate `farMass n ≤ (pressure n + |t| probeBound n)/(scale n * gap)`
with a positive gap.  If the normalized pressure divided by the scale vanishes,
then the explicit correction bound admits a vanishing sequence.  This is the
analytic composition of the probe modulus, the far-mass estimate and the
relative kinetic error. -/
theorem tendsto_probeCorrectionBound_of_pressure
    {t G Gb : ℝ} {modulus : ℝ → ℝ}
    {ρ farMass pressure probeBound scale ε : ℕ → ℝ} {gap : ℝ}
    (hω : Tendsto modulus (𝓝 0) (𝓝 0))
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0))
    (hgap : 0 < gap)
    (hfarNonneg : ∀ n, 0 ≤ farMass n)
    (hfarBound : ∀ n, farMass n ≤
      (pressure n + |t| * probeBound n) / (scale n * gap))
    (hpressure : Tendsto (fun n => (pressure n + |t| * probeBound n) / scale n)
      atTop (𝓝 0)) :
    Tendsto (fun n => probeCorrectionBound t G Gb modulus (ρ n) (farMass n) (ε n))
      atTop (𝓝 0) :=
  tendsto_probeCorrectionBound_zero hω hρ
    (tendsto_farMass_of_tendsto_pressure_div_scale hfarNonneg hfarBound hgap hpressure)
    hε

/-! ## 5. The additive relaxed per-cell comparison

The frozen comparison is additive: the expected normalized physical block is at
most the model block plus a correction.  We isolate the algebraic step which
turns a pointwise `(1 + 2 ε)` comparison into this additive form.  The law
bridge identifying the expected frozen block with `modelBlockSum / (n+1)` is an
explicit hypothesis. -/

section AdditiveRelaxedBlock

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*}

/-- **Additive relaxed per-cell comparison.**  Suppose the normalized physical
block is pointwise at most `(1 + 2 ε)` times the normalized model block plus a
correction, the expected model block is at most `modelSum`, the expected model
block is bounded by `Bnd`, and the expected correction is at most `δ`.  Then

`∫ phys ≤ modelSum + (2 ε Bnd + δ)`.

This is exactly the additive relaxed `hblock` consumed by the upper assembly,
with the multiplicative `(1 + 2 ε)` absorbed into the additive `2 ε Bnd`. -/
theorem integral_normalized_block_le_model_add
    (phys model corr : ι → Ω → ℝ)
    (modelSum Bnd δ ε : ℝ) (hε : 0 ≤ ε)
    (hpoint : ∀ c, ∀ᵐ ξ ∂P, phys c ξ ≤ (1 + 2 * ε) * model c ξ + corr c ξ)
    (hphys_int : ∀ c, Integrable (phys c) P)
    (hmodel_int : ∀ c, Integrable (model c) P)
    (hcorr_int : ∀ c, Integrable (corr c) P)
    (hmodel_law : ∀ c, ∫ ξ, model c ξ ∂P ≤ modelSum)
    (hmodel_bound : ∀ c, ∫ ξ, model c ξ ∂P ≤ Bnd)
    (hcorr : ∀ c, ∫ ξ, corr c ξ ∂P ≤ δ) :
    ∀ c, ∫ ξ, phys c ξ ∂P ≤ modelSum + (2 * ε * Bnd + δ) := by
  intro c
  have hpoint_int : Integrable (fun ξ => (1 + 2 * ε) * model c ξ + corr c ξ) P :=
    ((hmodel_int c).const_mul (1 + 2 * ε)).add (hcorr_int c)
  have hle : (∫ ξ, phys c ξ ∂P) ≤
      ∫ ξ, ((1 + 2 * ε) * model c ξ + corr c ξ) ∂P :=
    integral_mono_ae (hphys_int c) hpoint_int (hpoint c)
  have hcalc : (∫ ξ, ((1 + 2 * ε) * model c ξ + corr c ξ) ∂P) =
      (1 + 2 * ε) * (∫ ξ, model c ξ ∂P) + ∫ ξ, corr c ξ ∂P := by
    rw [integral_add ((hmodel_int c).const_mul _) (hcorr_int c), integral_const_mul]
  have hA := hmodel_bound c
  have hmul : (2 * ε) * (∫ ξ, model c ξ ∂P) ≤ (2 * ε) * Bnd :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have hB := hmodel_law c
  have hC := hcorr c
  rw [hcalc] at hle
  nlinarith

/-- **Vanishing of the additive relaxed error.**  If the relative kinetic error
and the expected correction tend to zero while the expected model block stays
bounded (indeed converges), then the additive error `2 ε Bnd + δ` tends to
zero. -/
theorem tendsto_two_mul_mul_add_zero
    {ε Bnd δ : ℕ → ℝ} {B : ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hBnd : Tendsto Bnd atTop (𝓝 B))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => 2 * ε n * Bnd n + δ n) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => 2 * ε n) atTop (𝓝 (2 * 0)) :=
    tendsto_const_nhds.mul hε
  have h := (h2.mul hBnd).add hδ
  simpa using h

end AdditiveRelaxedBlock


/-! ## 5b. The Finsler per-cell division by the sample size -/

section FinslerNormalizedDivision

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- Dividing the deterministic frozen tile comparison by the sample size
`n + 1` gives the normalized comparison with the additive correction term. -/
theorem finslerTileBlock_div_le_frozenModelTileBlock_div_add
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → ι) (X Y : Fin (n + 1) → M)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι)
    (frozenCost modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ)
    {ε B Gb : ℝ}
    (hcomp : finslerTileBlock F μ ν K hK hμ hν blockS blockT X Y φ k f t c ≤
      (1 + 2 * ε) * frozenModelTileBlock blockS blockT frozenCost modelProbe t c +
        (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) *
          (|t| * B + 2 * ε * (|t| * Gb))) :
    finslerTileBlock F μ ν K hK hμ hν blockS blockT X Y φ k f t c /
        ((n + 1 : ℕ) : ℝ) ≤
      (1 + 2 * ε) * (frozenModelTileBlock blockS blockT frozenCost modelProbe t c /
        ((n + 1 : ℕ) : ℝ)) +
      ((min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
        (|t| * B + 2 * ε * (|t| * Gb)) := by
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h := div_le_div_of_nonneg_right hcomp hNpos.le
  refine h.trans (le_of_eq ?_)
  field_simp

/-- The normalized Finsler tile block comparison, with the correction term
written additively.  The left side is exactly `finslerNormalizedTileBlock`. -/
theorem finslerNormalizedTileBlock_le_frozenModelTileBlock_add
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → Ω n → ι) (X Y : Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι) (ξ : Ω n)
    (frozenCost modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ)
    {ε B Gb : ℝ}
    (hcomp : finslerTileBlock F μ ν K hK hμ hν
      (fun i => blockS i ξ) (fun j => blockT j ξ)
      (fun i => X i ξ) (fun j => Y j ξ) φ k f t c ≤
      (1 + 2 * ε) * frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
        frozenCost modelProbe t c +
        (min (blockSizeS (fun i => blockS i ξ) c) (blockSizeT (fun j => blockT j ξ) c) : ℝ) *
          (|t| * B + 2 * ε * (|t| * Gb))) :
    finslerNormalizedTileBlock F μ ν K hK hμ hν blockS blockT X Y φ k f t c ξ ≤
      (1 + 2 * ε) * (frozenModelTileBlock (fun i => blockS i ξ) (fun j => blockT j ξ)
        frozenCost modelProbe t c / ((n + 1 : ℕ) : ℝ)) +
      ((min (blockSizeS (fun i => blockS i ξ) c) (blockSizeT (fun j => blockT j ξ) c) : ℝ) /
        ((n + 1 : ℕ) : ℝ)) *
        (|t| * B + 2 * ε * (|t| * Gb)) := by
  simpa only [finslerNormalizedTileBlock] using
    finslerTileBlock_div_le_frozenModelTileBlock_div_add μ ν K hK hμ hν
      (fun i => blockS i ξ) (fun j => blockT j ξ) (fun i => X i ξ) (fun j => Y j ξ)
      φ k f t c frozenCost modelProbe hcomp

end FinslerNormalizedDivision

end OTSelector.Reconstruction