import OTSelector.Reconstruction.PositiveComplianceBounds
import OTSelector.Reconstruction.OriginalSeedPairCoefficientContinuity

/-!
# Uniform coefficient bounds from the actual scalar separation

Every separated interior pair contains a fixed-length subinterval in a compact
interior region. The inverse compliance of those subintervals is bounded by
continuity. Semidefinite comparison transfers this bound to the full pair even
when its endpoints approach focal endpoints.
-/

open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

private theorem continuousOn_short_window_comp {V : Type*} [TopologicalSpace V]
    {f : ℝ × ℝ → V} {a b δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousOn f {p | p.1 ∈ Icc (a + δ / 4) (b - δ / 4) ∧
      p.2 ∈ Icc (a + δ / 4) (b - δ / 4) ∧ p.1 < p.2}) :
    ContinuousOn (fun x ↦ f (x + δ / 4, x + 3 * δ / 4)) (Icc a (b - δ)) := by
  have hwin : Continuous (fun x : ℝ ↦ (x + δ / 4, x + 3 * δ / 4)) :=
    (continuous_id.add continuous_const).prodMk (continuous_id.add continuous_const)
  apply hf.comp hwin.continuousOn
  intro x hx
  exact ⟨⟨by dsimp; linarith only [hx.1], by dsimp; linarith only [hx.2, hδ]⟩,
    ⟨by dsimp; linarith only [hx.1, hδ], by dsimp; linarith only [hx.2]⟩,
    by dsimp; linarith only [hδ]⟩

/-- Fixed-length interior windows give a continuous family of inverse compliances. -/
theorem continuousOn_short_inverse_compliance {n : Type*}
    [Fintype n] [DecidableEq n] {K : ℝ → Matrix n n ℝ} {a b δ : ℝ}
    (hδ : 0 < δ) (hspan : δ ≤ b - a)
    (hK : ContinuousOn K (Ioo a b)) (hpos : ∀ t ∈ Ioo a b, (K t).PosDef) :
    ContinuousOn (fun x ↦ (∫ t in (x + δ / 4)..(x + 3 * δ / 4), K t)⁻¹)
      (Icc a (b - δ)) := by
  have hsub : Icc (a + δ / 4) (b - δ / 4) ⊆ Ioo a b := by
    intro t ht
    constructor <;> linarith only [hδ, ht.1, ht.2]
  exact continuousOn_short_window_comp hδ
    (continuousOn_inverseIntervalCompliance (by linarith only [hδ, hspan])
      (hK.mono hsub) (fun t ht ↦ hpos t (hsub ht)))

/-- Removing two positive end pieces decreases the full compliance in matrix order. -/
theorem posSemidef_compliance_sub_short_window {n : Type*}
    [Fintype n] [DecidableEq n] {K : ℝ → Matrix n n ℝ} {x y l h : ℝ}
    (hxl : x ≤ l) (hlh : l ≤ h) (hhy : h ≤ y)
    (hK : ContinuousOn K (Icc x y)) (hpos : ∀ t ∈ Icc x y, (K t).PosSemidef) :
    ((∫ t in x..y, K t) - ∫ t in l..h, K t).PosSemidef := by
  have hint {s t : ℝ} (hs : s ∈ Icc x y) (ht : t ∈ Icc x y) :
      IntervalIntegrable K volume s t :=
    (hK.mono (ordConnected_Icc.uIcc_subset hs ht)).intervalIntegrable
  have hxy : x ≤ y := hxl.trans (hlh.trans hhy)
  have hx : x ∈ Icc x y := left_mem_Icc.mpr hxy
  have hy : y ∈ Icc x y := right_mem_Icc.mpr hxy
  have hl : l ∈ Icc x y := ⟨hxl, hlh.trans hhy⟩
  have hh : h ∈ Icc x y := ⟨hxl.trans hlh, hhy⟩
  have hleft := posSemidef_intervalIntegral hxl
    (fun t ht ↦ hpos t (Icc_subset_Icc le_rfl hl.2 ht))
  have hright := posSemidef_intervalIntegral hhy
    (fun t ht ↦ hpos t (Icc_subset_Icc hh.1 le_rfl ht))
  have hsum : (∫ t in x..y, K t) - (∫ t in l..h, K t) =
      (∫ t in x..l, K t) + (∫ t in h..y, K t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint hx hh) (hint hh hy),
      ← intervalIntegral.integral_add_adjacent_intervals (hint hx hl) (hint hl hh)]
    abel
  rw [hsum]
  exact hleft.add hright

/-- A positive scalar separation yields a uniform inverse-compliance bound on all
interior pairs, without boundedness or nondegeneracy at the two finite endpoints. -/
theorem exists_uniform_inverse_compliance_bound {n : Type*}
    [Fintype n] [DecidableEq n] {K : ℝ → Matrix n n ℝ} {a b δ : ℝ}
    (hδ : 0 < δ) (hspan : δ ≤ b - a)
    (hK : ContinuousOn K (Ioo a b)) (hpos : ∀ t ∈ Ioo a b, (K t).PosDef) :
    ∃ R ≥ 0, ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, δ ≤ y - x →
      ‖(∫ t in x..y, K t)⁻¹‖ ≤ R := by
  have hc := continuousOn_short_inverse_compliance hδ hspan hK hpos
  have htrace : ContinuousOn
      (fun x ↦ ((∫ t in (x + δ / 4)..(x + 3 * δ / 4), K t)⁻¹).trace)
      (Icc a (b - δ)) :=
    continuous_id.matrix_trace.comp_continuousOn hc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn htrace
  obtain ⟨R, hR, hnorm⟩ := exists_norm_bound_of_posSemidef_trace_le (n := n) C
  refine ⟨R, hR, fun x hx y hy hxy ↦ ?_⟩
  have hxy' : x < y := by linarith only [hδ, hxy]
  have hxrange : x ∈ Icc a (b - δ) := ⟨hx.1.le, by linarith only [hxy, hy.2]⟩
  have hlx : x + δ / 4 ∈ Ioo a b := by
    constructor <;> linarith only [hδ, hx.1, hxrange.2]
  have hhx : x + 3 * δ / 4 ∈ Ioo a b := by
    constructor <;> linarith only [hδ, hx.1, hxrange.2]
  have hpSmall : (∫ t in (x + δ / 4)..(x + 3 * δ / 4), K t).PosDef :=
    posDef_intervalIntegral (show x + δ / 4 < x + 3 * δ / 4 by linarith only [hδ]) (hK.mono (Icc_subset_Ioo hlx.1 hhx.2))
      (fun t ht ↦ hpos t (Icc_subset_Ioo hlx.1 hhx.2 ht))
  have hpFull : (∫ t in x..y, K t).PosDef :=
    posDef_intervalIntegral hxy' (hK.mono (Icc_subset_Ioo hx.1 hy.2))
      (fun t ht ↦ hpos t (Icc_subset_Ioo hx.1 hy.2 ht))
  have hdiff := posSemidef_compliance_sub_short_window
    (show x ≤ x + δ / 4 by linarith only [hδ])
    (show x + δ / 4 ≤ x + 3 * δ / 4 by linarith only [hδ])
    (show x + 3 * δ / 4 ≤ y by linarith only [hδ, hxy])
    (hK.mono (Icc_subset_Ioo hx.1 hy.2))
    (fun t ht ↦ (hpos t (Icc_subset_Ioo hx.1 hy.2 ht)).posSemidef)
  have hcompare := posSemidef_inverse_sub_inverse hpSmall hpFull hdiff
  apply hnorm _ hpFull.inv.posSemidef
  have htr := hcompare.trace_nonneg
  rw [Matrix.trace_sub] at htr
  exact (show (∫ t in x..y, K t)⁻¹.trace ≤
      (∫ t in (x + δ / 4)..(x + 3 * δ / 4), K t)⁻¹.trace by linarith only [htr]).trans
    ((le_abs_self _).trans (hC x hxrange))

end OTSelector.Reconstruction
