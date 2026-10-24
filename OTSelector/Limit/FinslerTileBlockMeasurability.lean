import OTSelector.Limit.FinslerExpectationUpperBound
import OTSelector.Limit.FinslerTileCountLaw

/-!
# Measurability of the physical tile block under random labels

The upper-bound assembly `OTSelector.Limit.FinslerExpectationUpperBound` takes the
per-cell integrability of the physical tile block

`ξ ↦ PartialMatching.maxCardValue (blockCost (blockS · ξ) (blockT · ξ) (cost ξ) c)`

as an explicit hypothesis `hintBlock`.  The obstruction to discharging it is that
the block matrix has a *random shape*: `blockCost` is indexed by
`Fin (#S_c ξ) → Fin (#T_c ξ)`, and the identification of the random block finset
with `Fin (#S_c ξ)` goes through the noncomputable `Finset.equivFin`, for which
no measurable selection exists.

This module proves that the block value is nevertheless measurable, by a route
that never needs to measure the enumeration separately.  The two ingredients are:

* the block value with *frozen* labels is a mesurable function of the ambient
  cost matrix (`measurable_blockValue_fixed` in
  `OTSelector.Limit.FinslerTileCountLaw`), because the enumeration is then a
  fixed function of a fixed finset;
* a function of a measurable map into a countable space with measurable
  singletons and a measurable second argument is measurable as soon as all its
  sections are (`measurable_comp_uncurry_of_forall`).

Applying the second with the (finite-valued, hence measurable) label-word map
`ξ ↦ ((fun i => blockS i ξ), (fun j => blockT j ξ))` yields measurability of the
random-label block value without any padded reformulation.  The padded-matrix
identity suggested in the task is therefore not needed for measurability; it
would only provide a fixed-size representation of the same value.

The concrete corollaries cover `Pressure.supportedTileBlock` and
`finslerNormalizedTileBlock`, together with the integrability of the latter from
the uniform tilted edge bound `k * 2 diam K + |t| ‖f‖` and the a.e. membership of
the sampled points in the compact carrier `K`.

No `sorry`, `admit` or added axiom occurs.
-/

open MeasureTheory ProbabilityTheory Filter Set Manifold OTSelector.Probability
open scoped BigOperators ENNReal NNReal Topology ContDiff BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Probability

variable {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β]
  [MeasurableSingletonClass β]

/-- **Composition with a discrete-valued measurable map.**

If `f` takes values in a countable space with measurable singletons, `g` is
measurable, and every section `F d` of a two-variable function is measurable,
then `a ↦ F (f a) (g a)` is measurable.  The proof writes the preimage of a
measurable set under `Function.uncurry F` as the countable union
`⋃ d, {d} ×ˢ (F d ⁻¹' s)` of measurable rectangles. -/
theorem measurable_comp_uncurry_of_forall {α δ γ ε : Type*}
    [MeasurableSpace α] [MeasurableSpace δ] [MeasurableSpace γ] [MeasurableSpace ε]
    [MeasurableSingletonClass δ] [Countable δ]
    {f : α → δ} {g : α → γ} {F : δ → γ → ε}
    (hf : Measurable f) (hg : Measurable g) (hF : ∀ d, Measurable (F d)) :
    Measurable fun a => F (f a) (g a) := by
  have huncurry : Measurable (Function.uncurry F) := by
    intro s hs
    have hEq : Function.uncurry F ⁻¹' s = ⋃ d : δ, {d} ×ˢ (F d ⁻¹' s) := by
      ext p
      constructor
      · intro hp
        refine Set.mem_iUnion.mpr ⟨p.1, ?_⟩
        exact Set.mem_prod.mpr ⟨rfl, hp⟩
      · intro hp
        obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hp
        obtain ⟨h1, h2⟩ := Set.mem_prod.mp hd
        rw [Set.mem_singleton_iff] at h1
        show F p.1 p.2 ∈ s
        rw [h1]
        exact h2
    rw [hEq]
    exact MeasurableSet.iUnion fun d => (MeasurableSet.singleton d).prod (hF d hs)
  exact huncurry.comp (hf.prodMk hg)

/-- **Measurability of the random block finset.**

This is the first step of the padded-matrix route: the map
`ξ ↦ blockFinset (blockS · ξ) c` into the finite type of finsets is measurable,
since `i ∈ blockFinset (blockS · ξ) c` is the measurable event
`blockS i ξ = c`.  (The subsequent enumeration step is not needed below: the
frozen-label route proves measurability of the block *value* without it.) -/
theorem measurable_blockFinset_random {α : Type*} [MeasurableSpace α]
    (blockS : Fin N → α → β) (c : β) (hS : ∀ i, Measurable (blockS i)) :
    Measurable fun a => blockFinset (fun i => blockS i a) c := by
  rw [measurable_finset_iff]
  intro i
  have h : (fun a => i ∈ blockFinset (fun i => blockS i a) c) =
      (fun a => blockS i a = c) := by
    funext a
    simp only [mem_blockFinset]
  rw [h]
  exact measurableSet_setOfPred.mp ((hS i) (measurableSet_singleton c))

/-- The maximum-cardinality block value with frozen labels, as a function of the
ambient cost matrix.  The block enumeration is computed from the fixed labels,
so this is a fixed (noncomputable) function of the matrix. -/
noncomputable def blockValueOfLabels (u v : Fin N → β) (D : Fin N → Fin N → ℝ)
    (t : β) : ℝ :=
  PartialMatching.maxCardValue (blockCost u v D t)

/-- With frozen labels, the block value is a measurable function of the ambient
cost matrix. -/
theorem measurable_blockValueOfLabels_snd (u v : Fin N → β) (t : β) :
    Measurable fun D : Fin N → Fin N → ℝ => blockValueOfLabels u v D t := by
  have h := measurable_blockValue_fixed (N := N) (β := β) u v
    (fun D : Fin N → Fin N → ℝ => D)
    (fun i j => (measurable_pi_apply (a := j)).comp (measurable_pi_apply (a := i))) t
  simpa only [blockValueOfLabels] using h

/-- **Measurability of the physical block value under random labels.**

For measurable random label maps `blockS`, `blockT` and a cost family whose
entries are measurable, the maximum-cardinality value of the random block matrix
is measurable.  This is the missing `hintBlock`-measurability statement.

The proof composes the frozen-label block value with the label-word map
`a ↦ ((fun i => blockS i a), (fun j => blockT j a))`, which takes values in the
finite type `(Fin N → β) × (Fin N → β)` and is therefore measurable with
measurable singletons.  No measurable enumeration of the random block is
selected. -/
theorem measurable_blockValue_random {α : Type*} [MeasurableSpace α]
    (blockS blockT : Fin N → α → β) (c : α → Fin N → Fin N → ℝ) (t : β)
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hc : ∀ i j, Measurable fun a => c a i j) :
    Measurable fun a =>
      PartialMatching.maxCardValue
        (blockCost (fun i => blockS i a) (fun j => blockT j a) (c a) t) := by
  classical
  have hL : Measurable fun a => ((fun i => blockS i a), (fun j => blockT j a)) :=
    (measurable_pi_lambda (fun a => fun i => blockS i a) hS).prodMk
      (measurable_pi_lambda (fun a => fun j => blockT j a) hT)
  have hC : Measurable c :=
    measurable_pi_lambda c fun i =>
      measurable_pi_lambda (fun a => c a i) fun j => hc i j
  have h := measurable_comp_uncurry_of_forall
    (f := fun a => ((fun i => blockS i a), (fun j => blockT j a)))
    (g := c) (F := fun p (D : Fin N → Fin N → ℝ) => blockValueOfLabels p.1 p.2 D t)
    hL hC fun p => measurable_blockValueOfLabels_snd p.1 p.2 t
  simpa only [blockValueOfLabels] using h

end OTSelector.Probability

namespace OTSelector.PartialMatching

/-- **Absolute bound on the maximum-cardinality value.**

If every edge cost is bounded in absolute value by `B ≥ 0`, then the
maximum-cardinality value is bounded in absolute value by `min m n * B`: every
maximum-cardinality matching has `min m n` edges, and the value is the infimum
of their costs. -/
theorem abs_maxCardValue_le_of_abs_le {m n : ℕ} {D : Fin m → Fin n → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i j, |D i j| ≤ B) :
    |maxCardValue D| ≤ (min m n : ℝ) * B := by
  classical
  let C : ℝ := (min m n : ℝ) * B
  set S : Set ℝ := {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost D}
    with hS
  have hSne : S.Nonempty :=
    ⟨_, diagonal m n, card_diagonal m n, rfl⟩
  have hmem : ∀ v ∈ S, |v| ≤ C := by
    rintro v ⟨σ, hσ, rfl⟩
    have hcard : (σ.card : ℝ) = (min m n : ℝ) := by exact_mod_cast hσ
    have hcost : |σ.cost D| ≤ (σ.card : ℝ) * B := by
      unfold cost
      calc |∑ e ∈ σ.edges, D e.1 e.2| ≤ ∑ e ∈ σ.edges, |D e.1 e.2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ e ∈ σ.edges, B := Finset.sum_le_sum fun e _ => hB e.1 e.2
        _ = (σ.edges.card : ℝ) * B := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hval : |σ.cost D| ≤ C := by
      rw [show C = (min m n : ℝ) * B from rfl, ← hcard]
      exact hcost
    simpa only [card] using hval
  have hbdd : BddBelow S :=
    ⟨-C, fun v hv => (abs_le.mp (hmem v hv)).1⟩
  show |maxCardValue D| ≤ C
  rw [abs_le]
  constructor
  · rw [maxCardValue]
    exact le_csInf hSne fun v hv => (abs_le.mp (hmem v hv)).1
  · rw [maxCardValue]
    exact (csInf_le hbdd (show (diagonal m n).cost D ∈ S from
      ⟨diagonal m n, card_diagonal m n, rfl⟩)).trans (abs_le.mp (hmem _ ⟨diagonal m n,
        card_diagonal m n, rfl⟩)).2

end OTSelector.PartialMatching

namespace OTSelector.Probability

variable {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β] [MeasurableSpace β]
  [MeasurableSingletonClass β]

/-- **Integrability of the random-label block value.**

A measurable block value whose ambient edge costs are uniformly bounded by `B`
is integrable: the block value is bounded in absolute value by
`min (#S_c) (#T_c) * B`, and both block sizes are at most `N`. -/
theorem integrable_blockValue_random {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsFiniteMeasure P]
    (blockS blockT : Fin N → α → β) (c : α → Fin N → Fin N → ℝ) (t : β) {B : ℝ}
    (hmeas : Measurable fun a =>
      PartialMatching.maxCardValue
        (blockCost (fun i => blockS i a) (fun j => blockT j a) (c a) t))
    (hB0 : 0 ≤ B) (hB : ∀ a i j, |c a i j| ≤ B) :
    Integrable (fun a =>
      PartialMatching.maxCardValue
        (blockCost (fun i => blockS i a) (fun j => blockT j a) (c a) t)) P := by
  refine Integrable.of_bound hmeas.aestronglyMeasurable ((N : ℝ) * B) ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  have hbound := PartialMatching.abs_maxCardValue_le_of_abs_le
    (D := blockCost (fun i => blockS i a) (fun j => blockT j a) (c a) t)
    (B := B) hB0 fun i j => hB a _ _
  refine hbound.trans ?_
  apply mul_le_mul_of_nonneg_right _ hB0
  exact_mod_cast le_trans (Nat.min_le_left _ _) (blockSizeS_le (fun i => blockS i a) t)

end OTSelector.Probability

namespace OTSelector.Pressure

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Measurability of the physical tile block with random labels.**

The cost entries are the tilted distance-slack costs
`k * (dist (X i) (Y j) - φ (Y j) + φ (X i)) + t * f (proj (X i), proj (Y j))`.
Each entry is measurable in `ξ` from measurability of the coordinate maps, of
the potential `φ`, and of the support projections.  The block value is then
measurable by `measurable_blockValue_random`. -/
theorem measurable_supportedTileBlock_random {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [SecondCountableTopology M]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (blockS blockT : Fin n → Ω → ι) (X Y : Fin n → Ω → M)
    (φ : M → ℝ) (hφ : Measurable φ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι)
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j)) :
    Measurable fun ξ => supportedTileBlock μ ν K hK hμ hν
      (fun i => blockS i ξ) (fun j => blockT j ξ)
      (fun i => X i ξ) (fun j => Y j ξ) φ k f t c := by
  classical
  have hcost : ∀ i j, Measurable fun ξ =>
      perturbedEdgeCost
        (fun i j => k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j)
        (fun i j => f (supportProjection μ K hK hμ (X i ξ),
          supportProjection ν K hK hν (Y j ξ))) t i j := by
    intro i j
    have hdist : Measurable fun ξ => dist (X i ξ) (Y j ξ) := (hX i).dist (hY j)
    have hφY : Measurable fun ξ => φ (Y j ξ) := hφ.comp (hY j)
    have hφX : Measurable fun ξ => φ (X i ξ) := hφ.comp (hX i)
    have hslack : Measurable fun ξ =>
        distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j := by
      unfold distanceSlackEdgeCost
      exact (hdist.sub hφY).add hφX
    have hprobe : Measurable fun ξ => f (supportProjection μ K hK hμ (X i ξ),
        supportProjection ν K hK hν (Y j ξ)) := by
      exact f.continuous.measurable.comp
        (((measurable_supportProjection μ K hK hμ).comp (hX i)).prodMk
          ((measurable_supportProjection ν K hK hν).comp (hY j)))
    unfold perturbedEdgeCost
    exact (hslack.const_mul k).add (hprobe.const_mul t)
  exact measurable_blockValue_random
    (blockS := fun i ξ => blockS i ξ) (blockT := fun j ξ => blockT j ξ)
    (c := fun ξ i j => perturbedEdgeCost
      (fun i j => k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j)
      (fun i j => f (supportProjection μ K hK hμ (X i ξ),
        supportProjection ν K hK hν (Y j ξ))) t i j)
    (t := c) (hS := hS) (hT := hT) (hc := hcost)

end OTSelector.Pressure

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- **Measurability of the normalized physical Finsler tile block.**

This is the `hintBlock` measurability statement for the concrete block function
of `OTSelector.Limit.FinslerExpectationUpperBound`, under measurable coordinate
maps, a measurable potential, and measurable labels. -/
theorem measurable_finslerNormalizedTileBlock
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (blockS blockT : Fin (n + 1) → Ω n → ι) (X Y : Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (hφ : Measurable φ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι)
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j)) :
    Measurable fun ξ => finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K
      hK.measurableSet hμ hν blockS blockT X Y φ k f t c ξ := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hblock : Measurable fun ξ =>
      Pressure.supportedTileBlock μ ν K hK.measurableSet hμ hν
        (fun i => blockS i ξ) (fun j => blockT j ξ)
        (fun i => X i ξ) (fun j => Y j ξ) φ k f t c :=
    Pressure.measurable_supportedTileBlock_random μ ν K hK.measurableSet hμ hν
      blockS blockT X Y φ hφ k f t c hS hT hX hY
  have hfinsler : Measurable fun ξ => finslerTileBlock (n := n) (ι := ι) F μ ν K
      hK.measurableSet hμ hν (fun i => blockS i ξ) (fun j => blockT j ξ)
      (fun i => X i ξ) (fun j => Y j ξ) φ k f t c := by
    simpa only [finslerTileBlock] using hblock
  have hnorm : Measurable fun ξ => finslerTileBlock (n := n) (ι := ι) F μ ν K
      hK.measurableSet hμ hν (fun i => blockS i ξ) (fun j => blockT j ξ)
      (fun i => X i ξ) (fun j => Y j ξ) φ k f t c / ((n + 1 : ℕ) : ℝ) :=
    hfinsler.div_const _
  simpa only [finslerNormalizedTileBlock] using hnorm

/-- **Integrability of the normalized physical Finsler tile block.**

On the event that all sampled points lie in the compact carrier `K`, every
tilted edge cost is bounded in absolute value by
`B = k * 2 diam K + |t| ‖f‖`.  Each block matching therefore has cost bounded
by `(n+1) * B`, so the block value is bounded by `(n+1) * B` in absolute value
and the normalized block by `B`.  Together with
`measurable_finslerNormalizedTileBlock`, this gives integrability by
`Integrable.of_bound`. -/
theorem integrable_finslerNormalizedTileBlock
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Measure (Ω n)) [IsProbabilityMeasure P]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (blockS blockT : Fin (n + 1) → Ω n → ι) (X Y : Fin (n + 1) → Ω n → M)
    (φ : M → ℝ)
    (hφ : let _instIntegrableTileBlockMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (hφmeas : Measurable φ)
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXK : ∀ᵐ ξ ∂P, ∀ i, X i ξ ∈ K) (hYK : ∀ᵐ ξ ∂P, ∀ j, Y j ξ ∈ K)
    (k : ℝ) (hk : 0 ≤ k) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι) :
    Integrable (fun ξ => finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K
      hK.measurableSet hμ hν blockS blockT X Y φ k f t c ξ) P := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hφ' : LipschitzWith 1 φ := hφ
  have hmeas := measurable_finslerNormalizedTileBlock (F := F) hcomplete
    μ ν K hK hμ hν blockS blockT X Y φ hφmeas k f t c hS hT hX hY
  -- The uniform tilted edge bound.
  let B : ℝ := k * (2 * finslerDiam F K) + |t| * (‖f‖₊ : ℝ)
  have hdiam : 0 ≤ finslerDiam F K := by
    simpa only [finslerDiam] using Metric.diam_nonneg (s := K)
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ k * (2 * finslerDiam F K) :=
      mul_nonneg hk (by linarith)
    exact add_nonneg h1 (mul_nonneg (abs_nonneg t) (by positivity))
  -- The a.e. entrywise bound.
  have hentry : ∀ᵐ ξ ∂P, ∀ i j,
      |perturbedEdgeCost
        (fun i j => k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j)
        (fun i j => f (supportProjection μ K hK.measurableSet hμ (X i ξ),
          supportProjection ν K hK.measurableSet hν (Y j ξ))) t i j| ≤ B := by
    filter_upwards [hXK, hYK] with ξ hXK' hYK'
    intro i j
    have hupper : perturbedEdgeCost
        (fun i j => k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j)
        (fun i j => f (supportProjection μ K hK.measurableSet hμ (X i ξ),
          supportProjection ν K hK.measurableSet hν (Y j ξ))) t i j ≤ B := by
      have h := Pressure.supportedTileEdgeCost_le (μ := μ) (ν := ν) (K := K)
        hK.measurableSet hμ hν (X := fun i => X i ξ) (Y := fun j => Y j ξ)
        (φ := φ) hφ' hK hXK' hYK' hk f t i j
      dsimp only [B]
      simpa only [perturbedEdgeCost, finslerDiam] using h
    have hlower : -B ≤ perturbedEdgeCost
        (fun i j => k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j)
        (fun i j => f (supportProjection μ K hK.measurableSet hμ (X i ξ),
          supportProjection ν K hK.measurableSet hν (Y j ξ))) t i j := by
      have hnonneg : 0 ≤ k * distanceSlackEdgeCost
          (fun i => X i ξ) (fun j => Y j ξ) φ i j :=
        mul_nonneg hk (distanceSlackEdgeCost_nonneg (fun i => X i ξ) (fun j => Y j ξ)
          φ hφ' i j)
      have hprobe_abs : |f (supportProjection μ K hK.measurableSet hμ (X i ξ),
          supportProjection ν K hK.measurableSet hν (Y j ξ))| ≤ (‖f‖₊ : ℝ) := by
        simpa only [coe_nnnorm, Real.norm_eq_abs] using
          f.norm_coe_le_norm (supportProjection μ K hK.measurableSet hμ (X i ξ),
            supportProjection ν K hK.measurableSet hν (Y j ξ))
      have hprobe : -( |t| * (‖f‖₊ : ℝ)) ≤
          t * f (supportProjection μ K hK.measurableSet hμ (X i ξ),
            supportProjection ν K hK.measurableSet hν (Y j ξ)) := by
        have hf_abs : |f (supportProjection μ K hK.measurableSet hμ (X i ξ),
            supportProjection ν K hK.measurableSet hν (Y j ξ))| ≤ (‖f‖₊ : ℝ) :=
          hprobe_abs
        have hmul : |t| * |f (supportProjection μ K hK.measurableSet hμ (X i ξ),
            supportProjection ν K hK.measurableSet hν (Y j ξ))| ≤ |t| * (‖f‖₊ : ℝ) :=
          mul_le_mul_of_nonneg_left hf_abs (abs_nonneg t)
        have hneg : -( |t| * (‖f‖₊ : ℝ)) ≤
            -( |t| * |f (supportProjection μ K hK.measurableSet hμ (X i ξ),
              supportProjection ν K hK.measurableSet hν (Y j ξ))|) := by
          linarith
        have hle : -( |t| * |f (supportProjection μ K hK.measurableSet hμ (X i ξ),
              supportProjection ν K hK.measurableSet hν (Y j ξ))|) ≤
            t * f (supportProjection μ K hK.measurableSet hμ (X i ξ),
              supportProjection ν K hK.measurableSet hν (Y j ξ)) := by
          rw [← abs_mul]
          exact neg_abs_le _
        linarith
      have hk2 : 0 ≤ k * (2 * finslerDiam F K) :=
        mul_nonneg hk (by linarith)
      have h1 : -(k * (2 * finslerDiam F K)) ≤
          k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j := by
        linarith
      have h2 : -( |t| * (‖f‖₊ : ℝ)) ≤
          t * f (supportProjection μ K hK.measurableSet hμ (X i ξ),
            supportProjection ν K hK.measurableSet hν (Y j ξ)) := hprobe
      have hsum := add_le_add h1 h2
      dsimp only [perturbedEdgeCost, B]
      calc -(k * (2 * finslerDiam F K) + |t| * (‖f‖₊ : ℝ))
          = -(k * (2 * finslerDiam F K)) + -( |t| * (‖f‖₊ : ℝ)) := by ring
        _ ≤ k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j +
              t * f (supportProjection μ K hK.measurableSet hμ (X i ξ),
                supportProjection ν K hK.measurableSet hν (Y j ξ)) := hsum
    exact abs_le.mpr ⟨hlower, hupper⟩
  -- The block value bound and its normalized form.
  have hbound : ∀ᵐ ξ ∂P,
      ‖finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        blockS blockT X Y φ k f t c ξ‖ ≤ B := by
    filter_upwards [hentry] with ξ hξ
    have hraw : |finslerTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (fun i => blockS i ξ) (fun j => blockT j ξ) (fun i => X i ξ) (fun j => Y j ξ)
        φ k f t c| ≤ ((n + 1 : ℕ) : ℝ) * B := by
      have hmin := PartialMatching.abs_maxCardValue_le_of_abs_le
        (D := blockCost (fun i => blockS i ξ) (fun j => blockT j ξ)
          (perturbedEdgeCost
            (fun i j => k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j)
            (fun i j => f (supportProjection μ K hK.measurableSet hμ (X i ξ),
              supportProjection ν K hK.measurableSet hν (Y j ξ))) t) c)
        hB0 (fun i j => hξ (blockEmbeddingS (fun i => blockS i ξ) c i)
          (blockEmbeddingT (fun j => blockT j ξ) c j))
      have hval : finslerTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
          (fun i => blockS i ξ) (fun j => blockT j ξ) (fun i => X i ξ) (fun j => Y j ξ)
          φ k f t c = PartialMatching.maxCardValue
            (blockCost (fun i => blockS i ξ) (fun j => blockT j ξ)
              (perturbedEdgeCost
                (fun i j => k * distanceSlackEdgeCost (fun i => X i ξ) (fun j => Y j ξ) φ i j)
                (fun i j => f (supportProjection μ K hK.measurableSet hμ (X i ξ),
                  supportProjection ν K hK.measurableSet hν (Y j ξ))) t) c) := rfl
      rw [hval]
      refine hmin.trans ?_
      apply mul_le_mul_of_nonneg_right _ hB0
      have hle : blockSizeS (fun i => blockS i ξ) c ≤ n + 1 :=
        blockSizeS_le (fun i => blockS i ξ) c
      exact_mod_cast le_trans (Nat.min_le_left _ _) hle
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [show finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet
        hμ hν blockS blockT X Y φ k f t c ξ =
        finslerTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
          (fun i => blockS i ξ) (fun j => blockT j ξ) (fun i => X i ξ) (fun j => Y j ξ)
          φ k f t c / ((n + 1 : ℕ) : ℝ) from rfl]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |finslerTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
          (fun i => blockS i ξ) (fun j => blockT j ξ) (fun i => X i ξ) (fun j => Y j ξ)
          φ k f t c| ≤ ((n + 1 : ℕ) : ℝ) * B := hraw
      _ = B * ((n + 1 : ℕ) : ℝ) := by ring
  exact Integrable.of_bound hmeas.aestronglyMeasurable B hbound

/-- **`hintBlock` from the marginal laws.**

The same integrability statement, with the a.e. membership in the compact
carrier derived from the marginal laws of the coordinate maps, exactly as in
`finslerExpectationUpperBound_of_block_model`.  This is the form in which the
integrability input `hintBlock` of the upper-bound assembly is discharged. -/
theorem integrable_finslerNormalizedTileBlock_of_laws
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Measure (Ω n)) [IsProbabilityMeasure P]
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (blockS blockT : Fin (n + 1) → Ω n → ι) (X Y : Fin (n + 1) → Ω n → M)
    (φ : M → ℝ)
    (hφ : let _instIntegrableTileBlockLawsMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (hφmeas : Measurable φ)
    (hS : ∀ i, Measurable (blockS i)) (hT : ∀ j, Measurable (blockT j))
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = (μ : Measure M))
    (hYlaw : ∀ j, P.map (Y j) = (ν : Measure M))
    (k : ℝ) (hk : 0 ≤ k) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι) :
    Integrable (fun ξ => finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K
      hK.measurableSet hμ hν blockS blockT X Y φ k f t c ξ) P := by
  have hXK : ∀ᵐ ξ ∂P, ∀ i, X i ξ ∈ K := by
    apply ae_all_iff.mpr
    intro i
    exact ae_of_ae_map (hX i).aemeasurable (by rw [hXlaw i]; exact hμ)
  have hYK : ∀ᵐ ξ ∂P, ∀ j, Y j ξ ∈ K := by
    apply ae_all_iff.mpr
    intro j
    exact ae_of_ae_map (hY j).aemeasurable (by rw [hYlaw j]; exact hν)
  exact integrable_finslerNormalizedTileBlock (F := F) hcomplete P μ ν K hK hμ hν
    blockS blockT X Y φ hφ hφmeas hS hT hX hY hXK hYK k hk f t c

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
