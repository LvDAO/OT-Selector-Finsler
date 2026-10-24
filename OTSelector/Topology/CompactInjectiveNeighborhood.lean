import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Topology.CompactInjectiveNeighborhood

Conditions: A map is continuous and locally injective along a compact set, and injective on that set; a parameter-family version includes an open ambient domain.

Objects: One open injective neighborhood, or one common product tube inside the given domain.

Proof detail: On the compact square, the relation f(x)=f(y)⇒x=y holds in a neighborhood: use local injectivity on the diagonal and Hausdorff separation off it. Apply the finite product/tube compactness argument.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6): Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products).

Source relation: Locally proved compact-tube corollary; no differentiability or local inverse theorem is assumed.
-/

/-!
# A common injective neighborhood of a compact central set

Continuity, local injectivity and injectivity on the compact central set suffice to
construct a single open injective neighborhood. For a family around a compact curve,
the tube lemma then supplies a common open parameter neighborhood for the whole curve.
-/

open Set Filter
open scoped Topology

namespace OTSelector.Geometry

variable {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace W]

/-- Local injectivity along a compact set and injectivity on that set give one open
injective neighborhood. Continuity is required only at points of the compact set. -/
theorem exists_open_injective_neighborhood_of_compact {K : Set X} (hK : IsCompact K)
    {f : X → Y} (hinj : InjOn f K) (hcont : ∀ x ∈ K, ContinuousAt f x)
    (hlocal : ∀ x ∈ K, ∃ U ∈ 𝓝 x, InjOn f U) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ InjOn f U := by
  let R : Set (X × X) := {p | f p.1 = f p.2 → p.1 = p.2}
  have hKK : K ×ˢ K ⊆ interior R := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply mem_interior_iff_mem_nhds.mpr
    by_cases heq : x = y
    · subst y
      obtain ⟨U, hU, hi⟩ := hlocal x hx
      filter_upwards [prod_mem_nhds hU hU] with p hp
      exact hi hp.1 hp.2
    · have hne : f x ≠ f y := fun h ↦ heq (hinj hx hy h)
      have hc₁ : ContinuousAt (fun p : X × X ↦ f p.1) (x, y) :=
        (hcont x hx).comp continuousAt_fst
      have hc₂ : ContinuousAt (fun p : X × X ↦ f p.2) (x, y) :=
        (hcont y hy).comp continuousAt_snd
      filter_upwards [(hc₁.ne_iff_eventually_ne hc₂).mp hne] with p hp
      exact fun h ↦ (hp h).elim
  obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ :=
    generalized_tube_lemma hK hK isOpen_interior hKK
  refine ⟨U ∩ V, hU.inter hV, fun x hx ↦ ⟨hKU hx, hKV hx⟩, ?_⟩
  intro x hx y hy heq
  have hr : (x, y) ∈ R := interior_subset (hUV ⟨hx.1, hy.2⟩)
  exact hr heq

/-- A compact injective central curve and local injectivity along it give a common
open tube, contained in any prescribed open domain around that central curve. -/
theorem exists_common_injective_tube {K : Set X} (hK : IsCompact K) {w₀ : W}
    {f : X × W → Y} {Ω : Set (X × W)} (hΩ : IsOpen Ω)
    (hKΩ : K ×ˢ {w₀} ⊆ Ω) (hinj : InjOn (fun t ↦ f (t, w₀)) K)
    (hcont : ∀ t ∈ K, ContinuousAt f (t, w₀))
    (hlocal : ∀ t ∈ K, ∃ U ∈ 𝓝 (t, w₀), InjOn f U) :
    ∃ (T : Set X) (V : Set W), IsOpen T ∧ IsOpen V ∧ K ⊆ T ∧ w₀ ∈ V ∧
      T ×ˢ V ⊆ Ω ∧ InjOn f (T ×ˢ V) := by
  have hi : InjOn f (K ×ˢ {w₀}) := by
    rintro ⟨t, w⟩ ⟨ht, hw⟩ ⟨s, v⟩ ⟨hs, hv⟩ heq
    rcases mem_singleton_iff.mp hw with rfl
    rcases mem_singleton_iff.mp hv with rfl
    exact Prod.ext (hinj ht hs heq) rfl
  obtain ⟨U, hU, hKU, hUi⟩ := exists_open_injective_neighborhood_of_compact
    (hK.prod isCompact_singleton) hi
    (by rintro ⟨t, w⟩ ⟨ht, rfl⟩; exact hcont t ht)
    (by rintro ⟨t, w⟩ ⟨ht, rfl⟩; exact hlocal t ht)
  obtain ⟨T, V, hT, hV, hKT, hwV, hTV⟩ :=
    generalized_tube_lemma hK isCompact_singleton (hU.inter hΩ)
      (fun p hp ↦ ⟨hKU hp, hKΩ hp⟩)
  exact ⟨T, V, hT, hV, hKT, hwV (mem_singleton w₀),
    fun p hp ↦ (hTV hp).2, hUi.mono fun p hp ↦ (hTV hp).1⟩

end OTSelector.Geometry
