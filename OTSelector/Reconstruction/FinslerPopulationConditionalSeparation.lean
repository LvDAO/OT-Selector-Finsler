import OTSelector.Reconstruction.FinslerPopulationCommonSupport
import OTSelector.Transport.CalibratedFiberIsometry
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Original physical separation in the actual conditional clock

The original compact disjoint carriers determine one positive separation constant.
The already selected geometric labels make the original potential an isometry on
each fiber, so that same separation and the physical carrier diameter hold for the
supports of the original scalar conditional laws.
-/

open Set MeasureTheory ProbabilityTheory Manifold
open scoped Topology ENNReal ContDiff

noncomputable section
namespace OTSelector.Reconstruction

/-- Compact scalar supports retaining a uniform physical separation and diameter bound. -/
structure ConditionalClockSupportBounds (μ ν : Measure ℝ) (δ D : ℝ) : Prop where
  source_compact : IsCompact μ.support
  target_compact : IsCompact ν.support
  separated : ∀ s ∈ μ.support, ∀ t ∈ ν.support, δ ≤ dist s t
  diameter : ∀ s ∈ μ.support ∪ ν.support,
    ∀ t ∈ μ.support ∪ ν.support, dist s t ≤ D

/-- Every legal coupling of the original two conditional laws retains their physical gap. -/
theorem ConditionalClockSupportBounds.ae_clock_gap_of_coupling
    {μ ν : Measure ℝ} {δ D : ℝ} (h : ConditionalClockSupportBounds μ ν δ D)
    {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π μ ν)
    (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) : ∀ᵐ p ∂π, δ ≤ p.2 - p.1 := by
  have hs : ∀ᵐ p ∂π, p.1 ∈ μ.support :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact μ.support_mem_ae)
  have ht : ∀ᵐ p ∂π, p.2 ∈ ν.support :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact ν.support_mem_ae)
  filter_upwards [hs, ht, horder] with p hp hq ho
  have hgap := h.separated p.1 hp p.2 hq
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ho)] at hgap
  linarith

/-- Original positive carrier separation upgrades legal weak clock order to strict order. -/
theorem ConditionalClockSupportBounds.ae_strict_order_of_coupling
    {μ ν : Measure ℝ} {δ D : ℝ} (h : ConditionalClockSupportBounds μ ν δ D)
    (hδ : 0 < δ) {π : Measure (ℝ × ℝ)} (hπ : Vlasov.IsCoupling π μ ν)
    (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) : ∀ᵐ p ∂π, p.1 < p.2 := by
  filter_upwards [h.ae_clock_gap_of_coupling hπ horder] with p hp
  linarith

variable {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z] [MeasurableEq Z]

/-- Both original conditional clock supports satisfy the same physical geometric bounds. -/
def PopulationConditionalSeparationLaw (u : M → ℝ) (a : M → Z) (lambda : Measure Z)
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (δ D : ℝ) : Prop :=
  ∀ᵐ z ∂lambda, ConditionalClockSupportBounds (condDistrib u a μ z) (condDistrib u a ν z) δ D

/-- Compact disjoint original carriers construct a positive uniform separation in the
same already selected original conditional laws, without a new potential or label choice. -/
theorem exists_population_conditional_separation (μ ν : Measure M)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : M → Z} (ha : Measurable a) (hbalance : μ.map a = ν.map a)
    {u : M → ℝ} (hu : Continuous u) {A B N : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hN : MeasurableSet N)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ x ∂ν, x ∈ N)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∃ δ : ℝ, 0 < δ ∧
      PopulationConditionalSeparationLaw u a (μ.map a) μ ν δ (Metric.diam (A ∪ B)) := by
  obtain ⟨δ, hδ, hgap⟩ := Metric.exists_pos_forall_lt_edist hA hB.isClosed hAB
  have hgap' (x : M) (hx : x ∈ A) (y : M) (hy : y ∈ B) : (δ : ℝ) ≤ dist x y := by
    have h := hgap x hx y hy
    rw [edist_nndist, ENNReal.coe_lt_coe] at h
    exact_mod_cast h.le
  have hbounds := ae_conditional_clock_support_bounds μ ν ha hbalance hu hA hB hN
    hμA hνB hμN hνN
    (fun _ hx _ hy heq ↦ dist_eq_clock_dist_of_ordered_calibration horder hx hy heq)
    hgap' (fun _ hx _ hy ↦ Metric.dist_le_diam_of_mem (hA.union hB).isBounded hx hy)
  have hmap₀ := ae_condDistrib_clock_eq_map_id μ a hu.measurable
  have hmap₁ := ae_condDistrib_clock_eq_map_id ν a hu.measurable
  rw [← hbalance] at hmap₁
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbounds, hmap₀, hmap₁] with z hz h₀ h₁
  rw [h₀, h₁]
  exact ⟨hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩

section SeedSpan

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
  {F : OTSelector.Geometry.ContinuousFinslerNorm E X} {u : X → ℝ}

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The true common seed span inherits the original positive separation and carrier diameter. -/
theorem ConditionalClockSupportBounds.span_length_bounds
    {S : F.CalibratedLevelSeedPatch u} {w : S.covector.ker}
    {μ ν : Measure ℝ} {δ D lo hi : ℝ}
    (h : ConditionalClockSupportBounds μ ν δ D) (hspan : CommonSeedSupportSpan S w μ ν lo hi) :
    δ ≤ hi - lo ∧ hi - lo ≤ D := by
  have := hspan.source.probability
  have := hspan.target.probability
  have hs : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  have ht : ∀ᵐ x ∂ν, x ∈ ν.support := ν.support_mem_ae
  obtain ⟨x, hx⟩ := hs.exists
  obtain ⟨y, hy⟩ := ht.exists
  have hxb := hspan.source.support_bounds x hx
  have hyb := hspan.target.support_bounds y hy
  have hd : dist x y ≤ hi - lo := by
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith [hxb.1, hxb.2, hyb.1, hyb.2]
  refine ⟨(h.separated x hx y hy).trans hd, ?_⟩
  have hdiam := h.diameter _ hspan.left_mem_support _ hspan.right_mem_support
  rw [Real.dist_eq, abs_of_nonpos (by linarith [hspan.lt])] at hdiam
  linarith

end SeedSpan

end OTSelector.Reconstruction
