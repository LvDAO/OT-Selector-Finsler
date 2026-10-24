import OTSelector.Reconstruction.FinslerConcreteUpperUniformCompactSplits

/-! The actual fixed compact colors have arbitrarily small total discarded
original mass, uniformly over all later dominated retained subpopulations. -/
open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E M Z T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [Fintype T]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {a : M → Z}
  {π : Measure (M × M)} [IsFiniteMeasure π]
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {q : ℕ}

/-- The actual compact/color approximation and its positive separation depth
are chosen once from the original retained components, before every later
original submeasure or changing microscopic grid is supplied. -/
theorem PopulationTypedCostData.exists_uniform_original_compact_subtype_splits_small_total
    (D : PopulationTypedCostData π μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (τ : T → Measure (M × M)) (hτ : ∀ t, τ t ≤ D.types.component t)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hreg : ∀ᵐ p ∂π, p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u)
    (hcal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    {C : Type*} [Fintype C] (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisjoint : Pairwise (Disjoint on cell))
    (hcover : ∀ t, ∀ᵐ p ∂τ t, a p.1 ∈ ⋃ c, cell c) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (K : T → C → Set (DyadicUnitCube q)) (depth : ℕ),
      0 < depth ∧ (∀ t c, IsCompact (K t c)) ∧
      (∀ k ≥ depth, ∀ t c c', ∀ x ∈ K t c, ∀ y ∈ K t c',
        dyadicCubeCell k x = dyadicCubeCell k y → c = c') ∧
      ∀ σ : T → Measure (M × M), (∀ t, σ t ≤ τ t) →
      (∀ t, compactColorGoodComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t) +
        ∑ c, compactColorBadComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t) c = σ t) ∧
      (∑ p : C × T, compactColorBadComponent (σ p.2) (fun z ↦ a z.1)
        (fun z ↦ D.sourceCoordinate p.2 z.1) cell (K p.2) p.1 Set.univ).toReal < θ ∧
      (∀ t, ∀ᵐ p ∂compactColorGoodComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t),
        ∃ c, a p.1 ∈ cell c ∧ a p.2 ∈ cell c ∧
          D.sourceCoordinate t p.1 ∈ K t c ∧ D.targetCoordinate t p.2 ∈ K t c) := by
  classical
  let ε : ℝ≥0∞ := ENNReal.ofReal (θ / (Fintype.card (C × T) + 1 : ℝ))
  have hε : ε ≠ 0 := by
    dsimp only [ε]
    positivity
  obtain ⟨K, depth, hd, hK, hsep, hall⟩ :=
    D.exists_uniform_original_compact_subtype_splits τ hτ hF hcomplete hu ha horder
      hreg hcal cell hcell hdisjoint hcover hε
  refine ⟨K, depth, hd, hK, hsep, ?_⟩
  intro σ hσ
  obtain ⟨hsplit, hsmall, hgood⟩ := hall σ hσ
  refine ⟨hsplit, ?_, hgood⟩
  let mass := fun p : C × T ↦ compactColorBadComponent (σ p.2) (fun z ↦ a z.1)
    (fun z ↦ D.sourceCoordinate p.2 z.1) cell (K p.2) p.1 Set.univ
  have hεfin : ε ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hmfin (p : C × T) : mass p ≠ (∞ : ℝ≥0∞) := ne_top_of_le_ne_top hεfin (hsmall p.2 p.1).le
  have hθ0 : 0 ≤ θ / (Fintype.card (C × T) + 1 : ℝ) := by positivity
  have hterm (p : C × T) : (mass p).toReal ≤ θ / (Fintype.card (C × T) + 1 : ℝ) := by
    simpa only [ε, ENNReal.toReal_ofReal hθ0] using
      ENNReal.toReal_mono hεfin (hsmall p.2 p.1).le
  have hsum : (∑ p : C × T, mass p).toReal ≤
      (Fintype.card (C × T) : ℝ) * (θ / (Fintype.card (C × T) + 1 : ℝ)) := by
    rw [ENNReal.toReal_sum (fun p _ ↦ hmfin p)]
    exact (Finset.sum_le_sum (fun p _ ↦ hterm p)).trans_eq
      (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
  refine hsum.trans_lt ?_
  have hden : (0 : ℝ) < Fintype.card (C × T) + 1 := by positivity
  calc (Fintype.card (C × T) : ℝ) * (θ / (Fintype.card (C × T) + 1 : ℝ)) =
      θ * Fintype.card (C × T) / (Fintype.card (C × T) + 1 : ℝ) := by ring
    _ < θ := (div_lt_iff₀ hden).mpr (by nlinarith)

end OTSelector.Reconstruction
