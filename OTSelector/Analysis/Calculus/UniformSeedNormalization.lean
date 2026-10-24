import OTSelector.Analysis.Calculus.CompactSmoothLipschitz
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformSeedNormalization.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformSeedNormalization`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C1 normalization is defined near a compact gradient graph, and the input covectors have the stated uniform first-order remainder.

Objects: Uniform first-jet preservation and remainder estimates after normalization.

Proof detail: Use a common compact neighborhood and uniform derivative continuity, apply the mean-value remainder bound and cancel the matched first derivatives.

Sources: Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Compact-uniform chain-rule corollary; there is no implicit Finsler or Hamiltonian premise.
-/

/-!
# Uniform transport of original first jets through smooth normalization

On the same compact core, an actual C1,1 derivative and its uniform ambient first
remainder give uniformly matching normalized seeds. The normalization is the given
C1 map on an open neighborhood of the original graph, not a separately chosen map
at each root. No Finsler phase representation is asserted here.
-/

open Set Metric
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The genuine ambient derivative remainder stays uniformly first order small
under the same smooth normalization of position and covector. Both actual and
affine model phases remain in its original open domain at the common radius. -/
theorem uniform_original_seed_normalization
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ G))
    {K : Set E} (hK : IsCompact K)
    {H : E → E →L[ℝ] E →L[ℝ] ℝ} (hH : ContinuousOn H K)
    (hrem : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
      ‖fderiv ℝ G (x + h) - fderiv ℝ G x - H x h‖ ≤ η * ‖h‖)
    {N : E × (E →L[ℝ] ℝ) → V} {U : Set (E × (E →L[ℝ] ℝ))}
    (hU : IsOpen U) (hN : ContDiffOn ℝ 1 N U)
    (hgraph : ∀ x ∈ K, (x, fderiv ℝ G x) ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
      (x + h, fderiv ℝ G (x + h)) ∈ U ∧
      (x + h, fderiv ℝ G x + H x h) ∈ U ∧
      ‖N (x + h, fderiv ℝ G (x + h)) -
        N (x + h, fderiv ℝ G x + H x h)‖ ≤ ε * ‖h‖ := by
  let Γ : Set (E × (E →L[ℝ] ℝ)) := (fun x ↦ (x, fderiv ℝ G x)) '' K
  have hΓ : IsCompact Γ := hK.image
    (continuous_id.prodMk (hG.continuous_fderiv one_ne_zero))
  have hΓU : Γ ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hgraph x hx
  obtain ⟨δ, hδ, _, hTU, A, hA⟩ :=
    exists_lipschitzOnWith_cthickening_of_contDiffOn hΓ hU hΓU hN
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := H) hH
  let C : ℝ := 1 + (L : ℝ) + max M 0
  have hC : 0 < C := by dsimp [C]; positivity
  have h1C : 1 ≤ C := by dsimp [C]; linarith [L.coe_nonneg, le_max_right M 0]
  have hLC : (L : ℝ) ≤ C := by dsimp [C]; linarith [le_max_right M 0]
  have hMC : M ≤ C := by dsimp [C]; linarith [le_max_left M 0, L.coe_nonneg]
  let η : ℝ := ε / ((A : ℝ) + 1)
  have hA1 : 0 < (A : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hA1
  have hAη : (A : ℝ) * η ≤ ε := by
    have heq : η * ((A : ℝ) + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hA1)
    nlinarith
  obtain ⟨r₀, hr₀, hsmall⟩ := hrem η hη
  refine ⟨min r₀ (δ / C), lt_min hr₀ (div_pos hδ hC), ?_⟩
  intro x hx h hh
  have hCh : C * ‖h‖ ≤ δ := by
    have hlt := (lt_div_iff₀ hC).mp (hh.trans_le (min_le_right _ _))
    nlinarith
  have hhδ : ‖h‖ ≤ δ :=
    (by nlinarith [norm_nonneg h] : ‖h‖ ≤ C * ‖h‖).trans hCh
  have hD : ‖fderiv ℝ G (x + h) - fderiv ℝ G x‖ ≤ δ := by
    have hb : ‖fderiv ℝ G (x + h) - fderiv ℝ G x‖ ≤ (L : ℝ) * ‖h‖ := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hLip.dist_le_mul (x + h) x
    exact hb.trans ((mul_le_mul_of_nonneg_right hLC (norm_nonneg _)).trans hCh)
  have hHh : ‖H x h‖ ≤ δ := by
    calc
      ‖H x h‖ ≤ ‖H x‖ * ‖h‖ := (H x).le_opNorm h
      _ ≤ C * ‖h‖ := mul_le_mul_of_nonneg_right ((hM x hx).trans hMC) (norm_nonneg _)
      _ ≤ δ := hCh
  have hxΓ : (x, fderiv ℝ G x) ∈ Γ := mem_image_of_mem _ hx
  have hactual : (x + h, fderiv ℝ G (x + h)) ∈ cthickening δ Γ := by
    apply mem_cthickening_of_dist_le _ (x, fderiv ℝ G x) δ Γ hxΓ
    rw [Prod.dist_eq]
    simpa only [dist_eq_norm, add_sub_cancel_left, max_le_iff] using
      And.intro hhδ hD
  have hmodel : (x + h, fderiv ℝ G x + H x h) ∈ cthickening δ Γ := by
    apply mem_cthickening_of_dist_le _ (x, fderiv ℝ G x) δ Γ hxΓ
    rw [Prod.dist_eq]
    simpa only [dist_eq_norm, add_sub_cancel_left, max_le_iff] using
      And.intro hhδ hHh
  refine ⟨hTU hactual, hTU hmodel, ?_⟩
  have htransport := hA.dist_le_mul _ hactual _ hmodel
  have hnorm : dist (x + h, fderiv ℝ G (x + h))
      (x + h, fderiv ℝ G x + H x h) =
      ‖fderiv ℝ G (x + h) - fderiv ℝ G x - H x h‖ := by
    rw [Prod.dist_eq, dist_self]
    simp only [dist_eq_norm, sub_add_eq_sub_sub, max_eq_right (norm_nonneg _)]
  rw [dist_eq_norm, hnorm] at htransport
  calc
    _ ≤ (A : ℝ) * ‖fderiv ℝ G (x + h) - fderiv ℝ G x - H x h‖ := htransport
    _ ≤ (A : ℝ) * (η * ‖h‖) := mul_le_mul_of_nonneg_left
      (hsmall x hx h (hh.trans_le (min_le_left _ _))) A.coe_nonneg
    _ = ((A : ℝ) * η) * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hAη (norm_nonneg _)

end OTSelector.Geometry

end
