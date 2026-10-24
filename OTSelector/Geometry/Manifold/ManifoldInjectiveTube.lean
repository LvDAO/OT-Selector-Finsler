import Mathlib.Geometry.Manifold.LocalDiffeomorph
import OTSelector.Analysis.Calculus.SmoothInjectiveTube
import OTSelector.Topology.CompactInjectiveNeighborhood
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ManifoldInjectiveTube.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ManifoldInjectiveTube`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual manifold family has invertible local differential along a compact central trace and the stated global injectivity on it.

Objects: A common smooth injective manifold tube and actual inverse.

Proof detail: Apply chartwise inverse function theorems, shrink around finitely many central neighborhoods and exclude off-diagonal collisions by compactness.

Sources: Jiří Lebl, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57 (https://www.jirka.org/ra/realanal2.pdf#page=51); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110); John M. Lee, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70 (https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10).
Relation: Compact-uniform inverse/tube corollary, derived from actual local derivatives and central injectivity.
-/

/-!
# A common manifold tube inverse across all charts along a compact center

The true coordinate differential in each central point's own chart gives a local
inverse of the original manifold-valued map. Compact injectivity then produces one
common tube and one smooth inverse, even when no chart contains the whole center.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {X W E M : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n M]

/-- An invertible actual derivative in the image point's own chart gives a local
manifold diffeomorphism of the original map, without a supplied local inverse. -/
theorem isLocalDiffeomorphAt_of_invertible_chart_fderiv
    {f : X × W → M} {Ω : Set (X × W)} (hΩ : IsOpen Ω) (hn : 1 ≤ n)
    (hf : ContMDiffOn 𝓘(ℝ, X × W) 𝓘(ℝ, E) n f Ω) {z : X × W} (hz : z ∈ Ω)
    (hi : (fderiv ℝ ((extChartAt 𝓘(ℝ, E) (f z)) ∘ f) z).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, X × W) 𝓘(ℝ, E) n f z := by
  let c := chartAt E (f z)
  let Q := Ω ∩ f ⁻¹' c.source
  have hQ : IsOpen Q := hf.continuousOn.isOpen_inter_preimage hΩ c.open_source
  have hzQ : z ∈ Q := ⟨hz, mem_chart_source E (f z)⟩
  have hc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) n c c.source := contMDiffOn_chart
  have hcoord : ContDiffOn ℝ n (c ∘ f) Q :=
    (hc.comp (hf.mono inter_subset_left) (fun _ hx ↦ hx.2)).contDiffOn
  have hi' : (fderiv ℝ (c ∘ f) z).IsInvertible := by
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using hi
  have hsingle : ({z.1} : Set X) ×ˢ {z.2} ⊆ Q := by
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    have hx' : x = z.1 := mem_singleton_iff.mp hx
    have hw' : w = z.2 := mem_singleton_iff.mp hw
    simpa only [hx', hw', Prod.eta] using hzQ
  obtain ⟨T, V, e, hT, hV, hKT, hwV, hTV, he, hes, _, hforward, hinverse⟩ :=
    exists_smooth_common_tube_inverse isCompact_singleton hQ hn hcoord hsingle
      (fun x hx y hy _ ↦ (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm)
      (by intro x hx; simpa only [mem_singleton_iff.mp hx, Prod.eta] using hi')
  let Φ : PartialDiffeomorph 𝓘(ℝ, X × W) 𝓘(ℝ, E) (X × W) E n :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := hforward.contMDiffOn
      contMDiffOn_invFun := hinverse.contMDiffOn }
  let χ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M n :=
    { c.symm.toPartialEquiv with
      open_source := c.open_target
      open_target := c.open_source
      contMDiffOn_toFun := contMDiffOn_chart_symm
      contMDiffOn_invFun := hc }
  have hze : z ∈ e.source := by rw [hes]; exact ⟨hKT (mem_singleton _), hwV⟩
  refine ⟨Φ.trans χ, ?_, ?_⟩
  · refine ⟨hze, ?_⟩
    change e z ∈ c.target
    rw [he]
    exact c.map_source hzQ.2
  · intro u hu
    change f u = c.symm (e u)
    rw [he]
    exact (c.left_inv (hTV (hes ▸ hu.1)).2).symm

omit [CompleteSpace X] [CompleteSpace W] [IsManifold 𝓘(ℝ, E) n M] in
private theorem localDiffeomorph_map_nhds {f : X × W → M} {z : X × W}
    (h : IsLocalDiffeomorphAt 𝓘(ℝ, X × W) 𝓘(ℝ, E) n f z) :
    Filter.map f (𝓝 z) = 𝓝 (f z) := by
  obtain ⟨Φ, hz, heq⟩ := h
  have hnear := Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds hz) heq
  have hm := Φ.toOpenPartialHomeomorph.map_nhds_eq hz
  change Filter.map (Φ.toPartialEquiv : X × W → M) (𝓝 z) = 𝓝 (Φ.toPartialEquiv z) at hm
  rw [← heq hz] at hm
  exact (Filter.map_congr hnear).trans hm

variable [T2Space M]

/-- The manifold-valued map is injective and a local diffeomorphism on one common
open tube. Each central point uses its own actual target chart derivative. -/
theorem exists_common_injective_tube_of_contMDiff {K : Set X} (hK : IsCompact K) {w₀ : W}
    {f : X × W → M} {Ω : Set (X × W)} (hΩ : IsOpen Ω) (hn : 1 ≤ n)
    (hf : ContMDiffOn 𝓘(ℝ, X × W) 𝓘(ℝ, E) n f Ω) (hKΩ : K ×ˢ {w₀} ⊆ Ω)
    (hinj : InjOn (fun t ↦ f (t, w₀)) K)
    (hinv : ∀ t ∈ K,
      (fderiv ℝ ((extChartAt 𝓘(ℝ, E) (f (t, w₀))) ∘ f) (t, w₀)).IsInvertible) :
    ∃ (T : Set X) (V : Set W), IsOpen T ∧ IsOpen V ∧ K ⊆ T ∧ w₀ ∈ V ∧
      T ×ˢ V ⊆ Ω ∧ InjOn f (T ×ˢ V) ∧
      ∀ z ∈ T ×ˢ V, IsLocalDiffeomorphAt 𝓘(ℝ, X × W) 𝓘(ℝ, E) n f z := by
  let R := {z | IsLocalDiffeomorphAt 𝓘(ℝ, X × W) 𝓘(ℝ, E) n f z}
  have hR : IsOpen R := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨Φ, hz, heq⟩ := hz
    filter_upwards [Φ.open_source.mem_nhds hz] with u hu
    exact ⟨Φ, hu, heq⟩
  have hcenter (t : X) (ht : t ∈ K) : (t, w₀) ∈ R :=
    isLocalDiffeomorphAt_of_invertible_chart_fderiv hΩ hn hf
      (hKΩ ⟨ht, mem_singleton _⟩) (hinv t ht)
  have hKsub : K ×ˢ {w₀} ⊆ Ω ∩ R := by
    rintro ⟨t, w⟩ ⟨ht, hw⟩
    have hw0 : w = w₀ := mem_singleton_iff.mp hw
    subst w
    exact ⟨hKΩ ⟨ht, mem_singleton _⟩, hcenter t ht⟩
  have hlocal (t : X) (ht : t ∈ K) : ∃ U ∈ 𝓝 (t, w₀), InjOn f U := by
    obtain ⟨Φ, hz, heq⟩ := hcenter t ht
    refine ⟨Φ.source, Φ.open_source.mem_nhds hz, ?_⟩
    intro u hu v hv huv
    apply Φ.toOpenPartialHomeomorph.injOn hu hv
    exact (heq hu).symm.trans (huv.trans (heq hv))
  obtain ⟨T, V, hT, hV, hKT, hwV, hTV, hi⟩ :=
    exists_common_injective_tube hK (hΩ.inter hR) hKsub hinj
      (fun t ht ↦ (hf.contMDiffAt (hΩ.mem_nhds (hKΩ ⟨ht, mem_singleton _⟩))).continuousAt)
      hlocal
  exact ⟨T, V, hT, hV, hKT, hwV, fun z hz ↦ (hTV hz).1, hi,
    fun z hz ↦ (hTV hz).2⟩

/-- One inverse of the actual manifold-valued map exists on a common tube around
the whole compact center, with the same manifold regularity in both directions.
No single target chart is required to contain that center. -/
theorem exists_manifold_common_tube_inverse {K : Set X} (hK : IsCompact K) {w₀ : W}
    {f : X × W → M} {Ω : Set (X × W)} (hΩ : IsOpen Ω) (hn : 1 ≤ n)
    (hf : ContMDiffOn 𝓘(ℝ, X × W) 𝓘(ℝ, E) n f Ω) (hKΩ : K ×ˢ {w₀} ⊆ Ω)
    (hinj : InjOn (fun t ↦ f (t, w₀)) K)
    (hinv : ∀ t ∈ K,
      (fderiv ℝ ((extChartAt 𝓘(ℝ, E) (f (t, w₀))) ∘ f) (t, w₀)).IsInvertible) :
    ∃ (T : Set X) (V : Set W) (e : OpenPartialHomeomorph (X × W) M),
      IsOpen T ∧ IsOpen V ∧ K ⊆ T ∧ w₀ ∈ V ∧ T ×ˢ V ⊆ Ω ∧
      (e : X × W → M) = f ∧ e.source = T ×ˢ V ∧ e.target = f '' (T ×ˢ V) ∧
      ContMDiffOn 𝓘(ℝ, X × W) 𝓘(ℝ, E) n e e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, X × W) n e.symm e.target := by
  obtain ⟨T, V, hT, hV, hKT, hwV, hTV, hi, hlocal⟩ :=
    exists_common_injective_tube_of_contMDiff hK hΩ hn hf hKΩ hinj hinv
  let S := T ×ˢ V
  have hS : IsOpen S := hT.prod hV
  have hopen : IsOpenMap (S.domRestrict f) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    have hm := localDiffeomorph_map_nhds (hlocal z z.property)
    change 𝓝 (f z) ≤ Filter.map (f ∘ (Subtype.val : S → X × W)) (𝓝 z)
    rw [← Filter.map_map, hS.isOpenEmbedding_subtypeVal.map_nhds_eq, hm]
  let pe := hi.toPartialEquiv f S
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe
    (hf.continuousOn.mono hTV) hopen hS
  have he : (e : X × W → M) = f := rfl
  have hes : e.source = S := rfl
  refine ⟨T, V, e, hT, hV, hKT, hwV, hTV, he, hes, rfl, hf.mono hTV, ?_⟩
  intro y hy
  have hs : e.symm y ∈ S := e.map_target hy
  have hl := hlocal (e.symm y) hs
  have hfy : f (e.symm y) = y := e.right_inv hy
  have hinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, X × W) n hl.localInverse y := by
    simpa only [hfy] using hl.localInverse_contMDiffAt
  have heq : e.symm =ᶠ[𝓝 y] hl.localInverse := by
    have hnear : ∀ᶠ q in 𝓝 y, e.symm q ∈ hl.localInverse.target :=
      (e.continuousAt_symm hy).preimage_mem_nhds
        (hl.localInverse.open_target.mem_nhds hl.localInverse_mem_target)
    filter_upwards [e.open_target.mem_nhds hy, hnear] with q hq hq'
    have h := hl.localInverse_left_inv hq'
    have hr : f (e.symm q) = q := e.right_inv hq
    rw [hr] at h
    exact h.symm
  exact (hinv.congr_of_eventuallyEq heq).contMDiffWithinAt

end OTSelector.Geometry

end
end
