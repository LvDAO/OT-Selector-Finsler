import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import OTSelector.Topology.CompactInjectiveNeighborhood
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SmoothInjectiveTube.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SmoothInjectiveTube`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual Cn map on Banach spaces has invertible differential along the compact central set and is injective on that set.

Objects: A common open product tube on which the actual map is injective with a Cn inverse.

Proof detail: Use local inverse neighborhoods, compact finite subcovers and an off-diagonal compactness argument to eliminate collisions.

Sources: Jiří Lebl, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57 (https://www.jirka.org/ra/realanal2.pdf#page=51); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Banach/compact-family generalization of the finite-dimensional inverse-function construction in the cited text.
-/

/-!
# A smooth inverse on one common tube around a compact central set

Invertibility of the actual derivative along an injective compact central set yields
one open product tube on which the original map is injective. The same map defines
an open partial homeomorphism on that whole tube, and its constructed inverse has
the same differentiability order. The source and target models may differ.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {X W Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem local_injective_of_contDiff {f : X × W → Y} {n : ℕ∞ω}
    (hn : 1 ≤ n) {z : X × W} (hf : ContDiffAt ℝ n f z)
    (hi : (fderiv ℝ f z).IsInvertible) : ∃ U ∈ 𝓝 z, InjOn f U := by
  obtain ⟨A, hA⟩ := hi
  have hd : HasFDerivAt f (A : (X × W) →L[ℝ] Y) z := by
    rw [hA]
    exact (hf.differentiableAt (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))).hasFDerivAt
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  let e := hf.toOpenPartialHomeomorph f hd hn0
  have hz : z ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hd hn0
  exact ⟨e.source, e.open_source.mem_nhds hz, e.injOn⟩

/-- Actual invertible derivatives along a compact injective center give one open
product tube contained in the supplied domain, with invertible derivative throughout. -/
theorem exists_common_injective_tube_of_contDiff {K : Set X} (hK : IsCompact K) {w₀ : W}
    {f : X × W → Y} {Ω : Set (X × W)} (hΩ : IsOpen Ω) {n : ℕ∞ω} (hn : 1 ≤ n)
    (hf : ContDiffOn ℝ n f Ω) (hKΩ : K ×ˢ {w₀} ⊆ Ω)
    (hinj : InjOn (fun t ↦ f (t, w₀)) K)
    (hinv : ∀ t ∈ K, (fderiv ℝ f (t, w₀)).IsInvertible) :
    ∃ (T : Set X) (V : Set W), IsOpen T ∧ IsOpen V ∧ K ⊆ T ∧ w₀ ∈ V ∧
      T ×ˢ V ⊆ Ω ∧ InjOn f (T ×ˢ V) ∧
      ∀ z ∈ T ×ˢ V, (fderiv ℝ f z).IsInvertible := by
  let R := Ω ∩ {z | (fderiv ℝ f z).IsInvertible}
  have hR : IsOpen R := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    refine inter_mem (hΩ.mem_nhds hz.1) ?_
    obtain ⟨A, hA⟩ := hz.2
    have hAn := A.nhds
    rw [hA] at hAn
    exact ((hf.continuousOn_fderiv_of_isOpen hΩ hn).continuousAt
      (hΩ.mem_nhds hz.1)).preimage_mem_nhds hAn
  have hKR : K ×ˢ {w₀} ⊆ R := by
    rintro ⟨t, w⟩ ⟨ht, hw⟩
    have hw0 : w = w₀ := mem_singleton_iff.mp hw
    subst w
    exact ⟨hKΩ ⟨ht, mem_singleton w₀⟩, hinv t ht⟩
  have hlocal (t : X) (ht : t ∈ K) : ∃ U ∈ 𝓝 (t, w₀), InjOn f U :=
    local_injective_of_contDiff hn
      (hf.contDiffAt (hΩ.mem_nhds (hKΩ ⟨ht, mem_singleton w₀⟩))) (hinv t ht)
  obtain ⟨T, V, hT, hV, hKT, hwV, hTV, hi⟩ := exists_common_injective_tube hK hR hKR
    hinj (fun t ht ↦ (hf.contDiffAt (hΩ.mem_nhds (hKΩ ⟨ht, mem_singleton w₀⟩))).continuousAt)
    hlocal
  exact ⟨T, V, hT, hV, hKT, hwV, fun z hz ↦ (hTV hz).1, hi,
    fun z hz ↦ (hTV hz).2⟩

/-- The original map itself admits a common smooth inverse on an open product tube
around the entire compact central set. No inverse or local injectivity is supplied. -/
theorem exists_smooth_common_tube_inverse {K : Set X} (hK : IsCompact K) {w₀ : W}
    {f : X × W → Y} {Ω : Set (X × W)} (hΩ : IsOpen Ω) {n : ℕ∞ω} (hn : 1 ≤ n)
    (hf : ContDiffOn ℝ n f Ω) (hKΩ : K ×ˢ {w₀} ⊆ Ω)
    (hinj : InjOn (fun t ↦ f (t, w₀)) K)
    (hinv : ∀ t ∈ K, (fderiv ℝ f (t, w₀)).IsInvertible) :
    ∃ (T : Set X) (V : Set W) (e : OpenPartialHomeomorph (X × W) Y),
      IsOpen T ∧ IsOpen V ∧ K ⊆ T ∧ w₀ ∈ V ∧ T ×ˢ V ⊆ Ω ∧
      (e : X × W → Y) = f ∧ e.source = T ×ˢ V ∧ e.target = f '' (T ×ˢ V) ∧
      ContDiffOn ℝ n e e.source ∧ ContDiffOn ℝ n e.symm e.target := by
  obtain ⟨T, V, hT, hV, hKT, hwV, hTV, hi, hreg⟩ :=
    exists_common_injective_tube_of_contDiff hK hΩ hn hf hKΩ hinj hinv
  let S := T ×ˢ V
  have hS : IsOpen S := hT.prod hV
  have hopen : IsOpenMap (S.domRestrict f) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    obtain ⟨A, hA⟩ := hreg z z.property
    have hfd := hf.contDiffAt (hΩ.mem_nhds (hTV z.property))
    have hd : HasFDerivAt f (A : (X × W) →L[ℝ] Y) z := by
      rw [hA]
      exact (hfd.differentiableAt (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))).hasFDerivAt
    have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
    have hmap := (hfd.hasStrictFDerivAt' hd hn0).map_nhds_eq_of_equiv
    change 𝓝 (f z) ≤ Filter.map (f ∘ (Subtype.val : S → X × W)) (𝓝 z)
    rw [← Filter.map_map, hS.isOpenEmbedding_subtypeVal.map_nhds_eq, hmap]
  let pe := hi.toPartialEquiv f S
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe
    (hf.continuousOn.mono hTV) hopen hS
  have he : (e : X × W → Y) = f := rfl
  have hes : e.source = S := rfl
  refine ⟨T, V, e, hT, hV, hKT, hwV, hTV, he, hes, rfl, hf.mono hTV, ?_⟩
  intro y hy
  have hs : e.symm y ∈ S := e.map_target hy
  obtain ⟨A, hA⟩ := hreg _ hs
  have hfd : ContDiffAt ℝ n e (e.symm y) := hf.contDiffAt (hΩ.mem_nhds (hTV hs))
  have hd : HasFDerivAt e (A : (X × W) →L[ℝ] Y) (e.symm y) := by
    rw [hA]
    exact (hfd.differentiableAt (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))).hasFDerivAt
  exact (e.contDiffAt_symm hy hd hfd).contDiffWithinAt

end OTSelector.Geometry

end
end
