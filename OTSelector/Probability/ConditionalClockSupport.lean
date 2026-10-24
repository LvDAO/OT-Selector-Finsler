import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Conditional Clock Support

Conditions: Finite original measures on a nonempty standard Borel metric space M; a measurable label with measurable equality; continuous real clock, compact full-measure carriers, a measurable common full carrier, and within-fiber distance preservation.

Objects: Actual condDistrib id a kernels and the supports of their clock images, with compact containment, cross separation, and a common diameter bound.

Proof detail: Transport the full-carrier label graph through joint disintegration. Place scalar supports in closures of actual fiber images. Transfer the distance bounds on those images and then to their closures; use compact carrier images to obtain compact supports.

Relation to primary sources: The support and distance conclusions are locally derived from disintegration and elementary closure. The proof needs neither closed label fibers nor absolute continuity of conditional laws. The two label marginals must coincide to put both conclusions on one common full-measure label set.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452E, p. 20: consistency and strong consistency; 452G(a)–(c), p. 21: probability kernels and concentration on fibers. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=20
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 41, 411N(b)–(e), p. 6: support, uniqueness, existence, and the closure of the continuous image of a support. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=6
-/
/-!
# Supports of actual conditional clock laws

The joint conditional-distribution identity places almost every conditional law on its
original full carrier and exact label fiber. A continuous real clock sends a compact carrier
into a compact set containing the entire scalar support.

When the clock preserves the original distances within each regular label fiber, uniform
cross-carrier separation and the carrier diameter bound pass to all scalar support points.
The proof uses the closure of each actual fiber image, so neither closed fibers nor absolute
continuity of conditional laws is required. All conditional kernels are the actual
`condDistrib id a` kernels of the original finite measures.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z]

/-- Actual conditional laws retain a full measurable carrier and their exact conditioning label. -/
theorem ae_condDistrib_mem_carrier_fiber (μ : Measure M) [IsFiniteMeasure μ]
    {a : M → Z} (ha : Measurable a) {S : Set M} (hS : MeasurableSet S)
    (hμS : ∀ᵐ x ∂μ, x ∈ S) :
    ∀ᵐ z ∂μ.map a, ∀ᵐ x ∂condDistrib id a μ z, x ∈ S ∧ a x = z := by
  have hmeas : MeasurableSet {p : Z × M | p.2 ∈ S ∧ a p.2 = p.1} :=
    (measurable_snd hS).inter (measurableSet_eq_fun (ha.comp measurable_snd) measurable_fst)
  have hgraph : ∀ᵐ p ∂μ.map (fun x ↦ (a x, x)), p.2 ∈ S ∧ a p.2 = p.1 := by
    apply (ae_map_iff (ha.prodMk measurable_id).aemeasurable hmeas).mpr
    exact hμS.mono fun _ hx ↦ ⟨hx, rfl⟩
  have hrec := compProd_map_condDistrib (mβ := inferInstance) (X := a) (Y := id)
    (measurable_id.aemeasurable : AEMeasurable (id : M → M) μ)
  simp only [id_eq] at hrec
  rw [← hrec] at hgraph
  exact Measure.ae_ae_of_ae_compProd hgraph

variable [MetricSpace M] [BorelSpace M]

omit [StandardBorelSpace M] [Nonempty M] [MetricSpace M] [BorelSpace M] in
private theorem support_map_subset_closure_image {ρ : Measure M} {u : M → ℝ}
    (hu : Measurable u) {S : Set M} (hρ : ∀ᵐ x ∂ρ, x ∈ S) :
    (ρ.map u).support ⊆ closure (u '' S) := by
  apply Measure.support_subset_of_isClosed isClosed_closure
  apply (ae_map_iff hu.aemeasurable isClosed_closure.measurableSet).mpr
  exact hρ.mono fun x hx ↦ subset_closure ⟨x, hx, rfl⟩

/-- A continuous clock sends each actual conditional law into the image of a compact carrier,
including every point of the scalar measure support. -/
theorem ae_support_map_condDistrib_subset_compact_image (μ : Measure M) [IsFiniteMeasure μ]
    {a : M → Z} (ha : Measurable a) {A : Set M} (hA : IsCompact A)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) {u : M → ℝ} (hu : Continuous u) :
    ∀ᵐ z ∂μ.map a, ((condDistrib id a μ z).map u).support ⊆ u '' A := by
  filter_upwards [ae_condDistrib_mem_carrier_fiber μ ha hA.measurableSet hμA] with z hz
  have hs := support_map_subset_closure_image hu.measurable (hz.mono fun _ h ↦ h.1)
  simpa only [(hA.image hu).isClosed.closure_eq] using hs

private theorem dist_le_on_closures {S T : Set ℝ} {D : ℝ}
    (h : ∀ s ∈ S, ∀ t ∈ T, dist s t ≤ D) :
    ∀ s ∈ closure S, ∀ t ∈ closure T, dist s t ≤ D := by
  intro s hs t ht
  have hs' : ∀ s ∈ S, dist s t ≤ D := by
    intro s hs
    exact closure_minimal (h s hs) (isClosed_le (continuous_const.dist continuous_id)
      continuous_const) ht
  exact closure_minimal hs' (isClosed_le (continuous_id.dist continuous_const)
    continuous_const) hs

private theorem le_dist_on_closures {S T : Set ℝ} {δ : ℝ}
    (h : ∀ s ∈ S, ∀ t ∈ T, δ ≤ dist s t) :
    ∀ s ∈ closure S, ∀ t ∈ closure T, δ ≤ dist s t := by
  intro s hs t ht
  have hs' : ∀ s ∈ S, δ ≤ dist s t := by
    intro s hs
    exact closure_minimal (h s hs) (isClosed_le continuous_const
      (continuous_const.dist continuous_id)) ht
  exact closure_minimal hs' (isClosed_le continuous_const
    (continuous_id.dist continuous_const)) hs

omit [StandardBorelSpace M] [Nonempty M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableEq Z] in
/-- Uniform original distance bounds on a common label fiber extend to every scalar support
point. Conditional fibers themselves need not be closed or absolutely continuous. -/
theorem scalar_support_bounds_of_ae_common_fiber {ρ σ : Measure M}
    {a : M → Z} {u : M → ℝ} (hu : Measurable u) {A B N : Set M} {z : Z}
    (hρ : ∀ᵐ x ∂ρ, x ∈ A ∩ N ∧ a x = z)
    (hσ : ∀ᵐ y ∂σ, y ∈ B ∩ N ∧ a y = z)
    (hclock : ∀ x ∈ N, ∀ y ∈ N, a x = a y → dist x y = dist (u x) (u y))
    {δ D : ℝ} (hgap : ∀ x ∈ A, ∀ y ∈ B, δ ≤ dist x y)
    (hdiam : ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, dist x y ≤ D) :
    (∀ s ∈ (ρ.map u).support, ∀ t ∈ (σ.map u).support, δ ≤ dist s t) ∧
    ∀ s ∈ (ρ.map u).support ∪ (σ.map u).support,
      ∀ t ∈ (ρ.map u).support ∪ (σ.map u).support, dist s t ≤ D := by
  let S : Set M := {x | x ∈ A ∩ N ∧ a x = z}
  let T : Set M := {x | x ∈ B ∩ N ∧ a x = z}
  have hs := support_map_subset_closure_image hu hρ
  have ht := support_map_subset_closure_image hu hσ
  change (ρ.map u).support ⊆ closure (u '' S) at hs
  change (σ.map u).support ⊆ closure (u '' T) at ht
  have hcross : ∀ s ∈ u '' S, ∀ t ∈ u '' T, δ ≤ dist s t := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← hclock x hx.1.2 y hy.1.2 (hx.2.trans hy.2.symm)]
    exact hgap x hx.1.1 y hy.1.1
  have hunion : ∀ s ∈ u '' (S ∪ T), ∀ t ∈ u '' (S ∪ T), dist s t ≤ D := by
    have hmem (x : M) (hx : x ∈ S ∪ T) : x ∈ A ∪ B ∧ x ∈ N ∧ a x = z := by
      rcases hx with hx | hx
      · exact ⟨Or.inl hx.1.1, hx.1.2, hx.2⟩
      · exact ⟨Or.inr hx.1.1, hx.1.2, hx.2⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hx' := hmem x hx
    have hy' := hmem y hy
    rw [← hclock x hx'.2.1 y hy'.2.1 (hx'.2.2.trans hy'.2.2.symm)]
    exact hdiam x hx'.1 y hy'.1
  have hsub : (ρ.map u).support ∪ (σ.map u).support ⊆ closure (u '' (S ∪ T)) := by
    rintro x (hx | hx)
    · exact closure_mono (image_mono subset_union_left) (hs hx)
    · exact closure_mono (image_mono subset_union_right) (ht hx)
  exact ⟨fun s hs' t ht' ↦ le_dist_on_closures hcross s (hs hs') t (ht ht'),
    fun s hs' t ht' ↦ dist_le_on_closures hunion s (hsub hs') t (hsub ht')⟩

/-- Actual conditional clock supports inherit the compact carriers, the original cross-distance
separation, and the carrier diameter bound on each common geometric label. -/
theorem ae_conditional_clock_support_bounds (μ ν : Measure M)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : M → Z} (ha : Measurable a) (hbalance : μ.map a = ν.map a)
    {u : M → ℝ} (hu : Continuous u) {A B N : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hN : MeasurableSet N)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (hclock : ∀ x ∈ N, ∀ y ∈ N, a x = a y → dist x y = dist (u x) (u y))
    {δ D : ℝ} (hgap : ∀ x ∈ A, ∀ y ∈ B, δ ≤ dist x y)
    (hdiam : ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, dist x y ≤ D) :
    ∀ᵐ z ∂μ.map a,
      ((condDistrib id a μ z).map u).support ⊆ u '' A ∧
      ((condDistrib id a ν z).map u).support ⊆ u '' B ∧
      IsCompact ((condDistrib id a μ z).map u).support ∧
      IsCompact ((condDistrib id a ν z).map u).support ∧
      (∀ s ∈ ((condDistrib id a μ z).map u).support,
        ∀ t ∈ ((condDistrib id a ν z).map u).support, δ ≤ dist s t) ∧
      ∀ s ∈ ((condDistrib id a μ z).map u).support ∪
          ((condDistrib id a ν z).map u).support,
        ∀ t ∈ ((condDistrib id a μ z).map u).support ∪
          ((condDistrib id a ν z).map u).support, dist s t ≤ D := by
  have hμfiber := ae_condDistrib_mem_carrier_fiber μ ha
    (hA.measurableSet.inter hN) (hμA.and hμN)
  have hνfiber := ae_condDistrib_mem_carrier_fiber ν ha
    (hB.measurableSet.inter hN) (hνB.and hνN)
  have hμimage := ae_support_map_condDistrib_subset_compact_image μ ha hA hμA hu
  have hνimage := ae_support_map_condDistrib_subset_compact_image ν ha hB hνB hu
  rw [← hbalance] at hνfiber hνimage
  filter_upwards [hμfiber, hνfiber, hμimage, hνimage] with z hzμ hzν hzA hzB
  have hb := scalar_support_bounds_of_ae_common_fiber hu.measurable hzμ hzν hclock hgap hdiam
  exact ⟨hzA, hzB,
    (hA.image hu).of_isClosed_subset Measure.isClosed_support hzA,
    (hB.image hu).of_isClosed_subset Measure.isClosed_support hzB, hb⟩

end OTSelector.Reconstruction
