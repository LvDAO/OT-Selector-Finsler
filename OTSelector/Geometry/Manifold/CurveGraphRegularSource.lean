import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.SameGraphInverse
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CurveGraphRegularSource.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CurveGraphRegularSource`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C2 position germ has positive longitudinal velocity and an actual local inverse, inside the prescribed open phase domain.

Objects: A common regular graph source neighborhood and actual inverse derivative.

Proof detail: Shrink the source using openness and continuity, apply the actual inverse differential formula and retain the range in the requested domain.

Sources: Jiří Lebl, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57 (https://www.jirka.org/ra/realanal2.pdf#page=51); Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Domain-control adapter for an existing graph inverse; it does not replace it by an unrelated inverse.
-/

/-!
# Regular source neighborhoods for a fixed actual graph inverse

A C² position germ and positive actual longitudinal velocity produce an open source
neighborhood inside any prescribed graph-phase domain. The given graph inverse is
retained, and its differentiability follows from that same velocity.
-/

open Set Filter
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Restrict the source of the same graph inverse to a constructed positive-velocity
neighborhood mapped into the supplied open graph-phase domain. -/
theorem exists_curveGraph_regular_source_of_contDiffAt
    {γ : W × ℝ → ℝ × V} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {q₀ : W × ℝ} (hγ₀ : ContDiffAt ℝ 2 γ q₀) (hq₀ : q₀ ∈ e.source)
    {D : Set (W × ℝ)} (hD : IsOpen D) (himage : curveGraphCoordinateMap γ q₀ ∈ D)
    (hv₀ : 0 < (fderiv ℝ γ q₀ (0, 1)).1) :
    ∃ U : Set (W × ℝ), IsOpen U ∧ q₀ ∈ U ∧ U ⊆ e.source ∧ MapsTo e U D ∧
      ContDiffOn ℝ 2 γ U ∧ ∀ q ∈ U,
        0 < (fderiv ℝ γ q (0, 1)).1 ∧ DifferentiableAt ℝ e.symm (e q) := by
  obtain ⟨U₀, hU₀sub, hU₀, hqU₀⟩ := mem_nhds_iff.mp (hγ₀.eventually (by norm_num))
  have hC2 (q : W × ℝ) (hq : q ∈ U₀) : ContDiffAt ℝ 2 γ q := hU₀sub hq
  have hγ : ContDiffOn ℝ 2 γ U₀ := fun q hq ↦ (hC2 q hq).contDiffWithinAt
  let U₁ := (e.source ∩ e ⁻¹' D) ∩ U₀
  have hU₁ : IsOpen U₁ :=
    (e.continuousOn.isOpen_inter_preimage e.open_source hD).inter hU₀
  have hqU₁ : q₀ ∈ U₁ := ⟨⟨hq₀, by rw [he]; exact himage⟩, hqU₀⟩
  have hvelocity : ContinuousOn (fun q ↦ (fderiv ℝ γ q (0, 1)).1) U₀ :=
    ((hγ.fderiv_of_isOpen hU₀ (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
      (contDiffOn_const (c := ((0 : W), (1 : ℝ))))).fst.continuousOn
  let U := U₁ ∩ {q | 0 < (fderiv ℝ γ q (0, 1)).1}
  have hU : IsOpen U :=
    (hvelocity.mono inter_subset_right).isOpen_inter_preimage hU₁ isOpen_Ioi
  refine ⟨U, hU, ⟨hqU₁, hv₀⟩, fun q hq ↦ hq.1.1.1,
    fun q hq ↦ hq.1.1.2, hγ.mono (fun q hq ↦ hq.1.2), ?_⟩
  intro q hq
  have hs : q ∈ e.source := hq.1.1.1
  have hd : DifferentiableAt ℝ γ q := (hC2 q hq.1.2).differentiableAt (by norm_num)
  refine ⟨hq.2, differentiableAt_curveGraphInverse_of_regular he (e.map_source hs) ?_ ?_⟩
  · simpa only [e.left_inv hs] using hd
  · simpa only [e.left_inv hs] using hq.2.ne'

end OTSelector.Geometry

end
