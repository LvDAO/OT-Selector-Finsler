import OTSelector.Geometry.FinslerCompleteGraphFocal
import Mathlib.Topology.DiscreteSubset

/-!
# Finitely many actual focal times in a compact part of one graph chart

The actual inverse-pole expansion gives invertibility in a punctured neighborhood of
every central time. Thus the singular times have no accumulation inside the graph domain,
and every compact subset of that domain contains finitely many singular times. Neither
an extra nonsingularity hypothesis nor continuity of an unrelated matrix family is used.
This result concerns the same graph chart and does not perform whole-segment chart gluing.
-/

open Set Filter Matrix Module
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Fintype ι] [DecidableEq ι]
  {bW : Basis ι ℝ W} {bV : Basis ι ℝ V}
  {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)} {w₀ : W}

/-- At every central time in the original graph domain, its actual position variation
is invertible at every sufficiently close distinct time, as supplied by the true pole. -/
theorem HasGraphFocalExpansion.eventually_det_ne_zero
    (h : HasGraphFocalExpansion bW bV Ψ D w₀) {t : ℝ} (ht : (w₀, t) ∈ D) :
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    ∀ᶠ s in 𝓝[≠] t, (J s).det ≠ 0 := by
  obtain ⟨U, R, K, hU, h0, _, _, hpole, _, _⟩ := (h t ht).2.1
  have hu : ∀ᶠ s in 𝓝 t, s - t ∈ U := by
    have hc : ContinuousAt (fun s : ℝ ↦ s - t) t :=
      continuousAt_id.sub continuousAt_const
    apply hc.preimage_mem_nhds
    simpa only [sub_self] using hU.mem_nhds h0
  filter_upwards [nhdsWithin_le_nhds hu, self_mem_nhdsWithin] with s hs hst
  have hne : s - t ≠ 0 := sub_ne_zero.mpr (by simpa using hst)
  have hp := (hpole (s - t) hs hne).1
  simpa only [add_sub_cancel] using hp

/-- In any compact subset of the central time domain of this same graph chart, the
actual position variation has only finitely many singular times. -/
theorem HasGraphFocalExpansion.finite_singular_times
    (h : HasGraphFocalExpansion bW bV Ψ D w₀) {K : Set ℝ}
    (hK : IsCompact K) (hKD : K ⊆ {t | (w₀, t) ∈ D}) :
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    {t ∈ K | (J t).det = 0}.Finite := by
  let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
  let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
  have hcod : {t | (J t).det ≠ 0} ∈ codiscreteWithin K := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro t ht
    filter_upwards [h.eventually_det_ne_zero (hKD ht)] with s hs
    exact Or.inl hs
  have hfinite := hK.finite_sdiff_of_mem_codiscreteWithin hcod
  exact hfinite.subset (fun _ ht ↦ ⟨ht.1, fun hne ↦ hne ht.2⟩)

end OTSelector.Geometry
