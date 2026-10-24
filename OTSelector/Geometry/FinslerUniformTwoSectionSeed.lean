import OTSelector.Geometry.FinslerUniformSeedNormalization
import OTSelector.Analysis.Calculus.UniformSecondJetLevelSection

/-!
# Uniform original and polynomial seeds on their own level sections

One large compact core is fixed before the error tolerance. The original section and
polynomial section are compared through the same inverse branch and normalization.
Only continuity of the actual second jets on the compact core is used.
-/

open Set Filter MeasureTheory Manifold Metric
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

private theorem uniform_section_displacement
    {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {U K : Set E} {B : Set W} (hU : IsOpen U) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hK : IsCompact K) (hKU : K ⊆ U) {ρ : E × W → E}
    (hρ : ContDiffOn ℝ 1 ρ (U ×ˢ B)) (hρ₀ : ∀ x ∈ K, ρ (x, 0) = x) :
    ∃ r > 0, ∃ A : ℝ≥0, ∀ x ∈ K, ∀ w : W, ‖w‖ < r →
      (x, w) ∈ U ×ˢ B ∧ ‖ρ (x, w) - x‖ ≤ (A : ℝ) * ‖w‖ := by
  let Z := (fun x : E ↦ (x, (0 : W))) '' K
  have hZ : IsCompact Z := hK.image (continuous_id.prodMk continuous_const)
  have hZU : Z ⊆ U ×ˢ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hKU hx, h0B⟩
  obtain ⟨r, hr, _, hsub, A, hA⟩ :=
    exists_lipschitzOnWith_cthickening_of_contDiffOn hZ (hU.prod hB) hZU hρ
  refine ⟨r, hr, A, ?_⟩
  intro x hx w hw
  have hxZ : (x, (0 : W)) ∈ Z := mem_image_of_mem _ hx
  have hz : (x, w) ∈ cthickening r Z := by
    apply mem_cthickening_of_dist_le _ (x, 0) r Z hxZ
    simpa using hw.le
  have h0z : (x, (0 : W)) ∈ cthickening r Z := self_subset_cthickening _ hxZ
  have hb := hA.dist_le_mul _ hz _ h0z
  refine ⟨hsub hz, ?_⟩
  have hdist : dist (x, w) (x, (0 : W)) = ‖w‖ := by simp
  simpa only [hdist, dist_eq_norm, hρ₀ x hx] using hb

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- On one large compact core, actual inverse states on the original allowed level
section and normalized polynomial states on their own section match uniformly to
first order. Both states retain their original slit-chart legality. -/
theorem exists_compact_uniform_twoSection_seed
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target) {c : ℝ} (hc : 0 < c)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hLip : LipschitzWith L (fderiv ℝ G))
    {C H U : Set E} (hHC : H ⊆ C) (hHU : H ⊆ U)
    {ν : Measure E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    (hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    (henergy : ∀ y ∈ C, F.chartEnergy old (eL.symm (y, fderiv ℝ G y)) = c)
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
    {O : Set (ScalarSecondJet E)} {B Bσ : Set p₀.ker}
    (hU : IsOpen U) (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : p₀.ker) ∈ B)
    (hBσ : IsOpen Bσ) (h0Bσ : (0 : p₀.ker) ∈ Bσ)
    (hHj : ∀ x ∈ H, (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    (hp : ∀ x ∈ H, (fderiv ℝ G x) v₀ ≠ 0)
    {ρ : E × p₀.ker → E} {σ : ScalarSecondJet E × p₀.ker → E}
    (hρ : ContDiffOn ℝ 1 ρ (U ×ˢ B)) (hσ : ContDiffOn ℝ 1 σ (O ×ˢ Bσ))
    (hρ₀ : ∀ x ∈ H, ρ (x, 0) = x) (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hρlevel : ∀ x ∈ H, ∀ w ∈ B, G (ρ (x, w)) = G x)
    (hσlevel : ∀ j ∈ O, ∀ w ∈ Bσ,
      scalarSecondJetPolynomial j (σ (j, w)) = j.2.1)
    (hρproj : ∀ x ∈ H, ∀ w ∈ B,
      ((covectorSplitting p₀ v₀ hp₀).symm (ρ (x, w) - x)).1 = w)
    (hσproj : ∀ j ∈ O, ∀ w ∈ Bσ,
      ((covectorSplitting p₀ v₀ hp₀).symm (σ (j, w) - j.1)).1 = w)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    let j : E → ScalarSecondJet E :=
      fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      (∀ η : ℝ, 0 < η → ∃ r > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
        ‖G (x + h) - scalarSecondJetPolynomial (j x) (x + h)‖ ≤ η * ‖h‖ ^ 2) ∧
      ∃ A₀ : ℝ≥0, ∀ η : ℝ, 0 < η → ∃ r > 0,
        ∀ x ∈ K, ∀ w : p₀.ker, ‖w‖ < r → ρ (x, w) ∈ C →
          (x, w) ∈ U ×ˢ B ∧ (j x, w) ∈ O ×ˢ Bσ ∧
          eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w))) ∈ chartEnergyDomain old ∧
          (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w))) ∈
            eL.target ∧
          F.covectorNormalization old eL c
            (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w))) ∈
            chartEnergyDomain old ∧
          ‖eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w))) -
            eL.symm (x, fderiv ℝ G x)‖ ≤ (A₀ : ℝ) * ‖w‖ ∧
          ‖F.covectorNormalization old eL c
              (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w))) -
            eL.symm (x, fderiv ℝ G x)‖ ≤ (A₀ : ℝ) * ‖w‖ ∧
          ‖eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w))) -
            F.covectorNormalization old eL c
              (σ (j x, w), fderiv ℝ (scalarSecondJetPolynomial (j x)) (σ (j x, w)))‖ ≤
            η * ‖w‖ := by
  obtain ⟨K, hKH, hK, hloss, hHK, hScalar, hsame⟩ :=
    hF.exists_compact_uniform_normalized_polynomial_seed old heL hsource hInv hc
      hG hLip hHC hH hνH hsecond hHess hlegal henergy hε
  let j : E → ScalarSecondJet E :=
    fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  have hj : ContinuousOn j K := continuousOn_id.prodMk
    (hG.continuous.continuousOn.prodMk
      ((hG.continuous_fderiv one_ne_zero).continuousOn.prodMk hHK))
  let Q : ScalarSecondJet E × E → E × (E →L[ℝ] ℝ) :=
    fun z ↦ (z.2, fderiv ℝ (scalarSecondJetPolynomial z.1) z.2)
  have hQ : ContDiff ℝ 1 Q := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact contDiffAt_snd.prodMk
      ((contDiffAt_fiberLegendre contDiff_scalarSecondJetPolynomial_joint.contDiffAt).of_le
        (by simp))
  let V := Q ⁻¹' eL.target
  have hV : IsOpen V := eL.open_target.preimage hQ.continuous
  let N : ScalarSecondJet E × E → E × E :=
    fun z ↦ F.covectorNormalization old eL c (Q z)
  obtain ⟨_, hN₀, hNspec⟩ := hF.covectorNormalization_spec old heL hsource hInv hc
  have hN : ContDiffOn ℝ 1 N V :=
    (hN₀.of_le (by simp)).comp hQ.contDiffOn (fun _ hz ↦ hz)
  let Z := (fun x ↦ (j x, x)) '' K
  have hZ : IsCompact Z := hK.image_of_continuousOn (hj.prodMk continuousOn_id)
  have hZV : Z ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    change (x, fderiv ℝ (scalarSecondJetPolynomial (j x)) x) ∈ eL.target
    rw [(hasFDerivAt_scalarSecondJetPolynomial_center (j x)).fderiv]
    exact hlegal x (hHC (hKH hx))
  obtain ⟨δ, hδ, _, hδV, A, hA⟩ :=
    exists_lipschitzOnWith_cthickening_of_contDiffOn hZ hV hZV hN
  obtain ⟨d, hd, R, hdisp⟩ := uniform_section_displacement hU hB h0B hK
    (hKH.trans hHU) hρ (fun x hx ↦ hρ₀ x (hKH hx))
  let D : ℝ := (R : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hRD : (R : ℝ) ≤ D := by dsimp [D]; linarith
  let A₀ : ℝ≥0 := A * (R + 1) + 1
  have hA₀ : (A₀ : ℝ) = (A : ℝ) * D + 1 := by simp [A₀, D]
  have hcenterN (x : E) (hx : x ∈ K) : N (j x, x) = eL.symm (x, fderiv ℝ G x) := by
    have hQcenter : Q (j x, x) = (x, fderiv ℝ G x) := by
      change (x, fderiv ℝ (scalarSecondJetPolynomial (j x)) x) = _
      rw [(hasFDerivAt_scalarSecondJetPolynomial_center (j x)).fderiv]
    change F.covectorNormalization old eL c (Q (j x, x)) = _
    rw [hQcenter]
    exact (hNspec _ (hlegal x (hHC (hKH hx)))).2.2.2.2 (henergy x (hHC (hKH hx)))
  refine ⟨K, hKH, hK, hloss, hHK, hScalar, A₀, ?_⟩
  intro ζ hζ
  let η := min ζ 1
  have hη : 0 < η := lt_min hζ zero_lt_one
  have hηζ : η ≤ ζ := min_le_left _ _
  have hη1 : η ≤ 1 := min_le_right _ _
  let a : ℝ := η / (2 * D)
  have ha : 0 < a := div_pos hη (mul_pos (by norm_num) hD)
  have haD : a * D = η / 2 := by dsimp [a]; field_simp
  obtain ⟨r₀, hr₀, h₀⟩ := hsame a ha
  let b : ℝ := min 1 (η / (2 * ((A : ℝ) + 1)))
  have hb : 0 < b := lt_min zero_lt_one (div_pos hη (by positivity))
  have hb1 : b ≤ 1 := min_le_left _ _
  have hAb : (A : ℝ) * b ≤ η / 2 := by
    have ha1 : 0 < (A : ℝ) + 1 := by positivity
    have hle := min_le_right (1 : ℝ) (η / (2 * ((A : ℝ) + 1)))
    have hmul := (le_div_iff₀ (show 0 < 2 * ((A : ℝ) + 1) by positivity)).mp hle
    change b * (2 * ((A : ℝ) + 1)) ≤ η at hmul
    nlinarith
  obtain ⟨r₁, hr₁, h₁⟩ := exists_uniform_secondJet_levelSection_error p₀ v₀ hp₀
    hU hO hB h0B hBσ h0Bσ hG.contDiffOn hK (hKH.trans hHU) hHK
    (fun x hx ↦ hHj x (hKH hx)) (fun x hx ↦ hp x (hKH hx)) hρ hσ
    (fun x hx ↦ hρ₀ x (hKH hx)) hσ₀ (fun x hx ↦ hρlevel x (hKH hx))
    hσlevel (fun x hx ↦ hρproj x (hKH hx)) hσproj hb
  refine ⟨min d (min r₁ (min (r₀ / D) (δ / D))),
    lt_min hd (lt_min hr₁ (lt_min (div_pos hr₀ hD) (div_pos hδ hD))), ?_⟩
  intro x hx w hw hC
  have hwD : ‖w‖ < d := hw.trans_le (min_le_left _ _)
  have hw1 : ‖w‖ < r₁ := hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hw0 : ‖w‖ < r₀ / D := hw.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hwδ : ‖w‖ < δ / D := hw.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hρbound := (hdisp x hx w hwD).2
  obtain ⟨hρdom, hσdom, hdiff⟩ := h₁ x hx w hw1
  have hρD : ‖ρ (x, w) - x‖ ≤ D * ‖w‖ :=
    hρbound.trans (mul_le_mul_of_nonneg_right hRD (norm_nonneg _))
  have hσD : ‖σ (j x, w) - x‖ ≤ D * ‖w‖ := by
    calc
      _ ≤ ‖σ (j x, w) - ρ (x, w)‖ + ‖ρ (x, w) - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ b * ‖w‖ + (R : ℝ) * ‖w‖ := add_le_add (by rwa [norm_sub_rev]) hρbound
      _ ≤ 1 * ‖w‖ + (R : ℝ) * ‖w‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)) le_rfl
      _ = D * ‖w‖ := by dsimp [D]; ring
  have hρsmall : ‖ρ (x, w) - x‖ < r₀ :=
    hρD.trans_lt (by nlinarith [(lt_div_iff₀ hD).mp hw0])
  have hsmallδ : D * ‖w‖ ≤ δ := by nlinarith [(lt_div_iff₀ hD).mp hwδ]
  have hcenterZ : (j x, x) ∈ Z := mem_image_of_mem _ hx
  have hρZ : (j x, ρ (x, w)) ∈ cthickening δ Z := by
    apply mem_cthickening_of_dist_le _ (j x, x) δ Z hcenterZ
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
    exact hρD.trans hsmallδ
  have hσZ : (j x, σ (j x, w)) ∈ cthickening δ Z := by
    apply mem_cthickening_of_dist_le _ (j x, x) δ Z hcenterZ
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
    exact hσD.trans hsmallδ
  have hσlegal : Q (j x, σ (j x, w)) ∈ eL.target := hδV hσZ
  have htransport := hA.dist_le_mul _ hρZ _ hσZ
  have hpairdist : dist (j x, ρ (x, w)) (j x, σ (j x, w)) =
      ‖ρ (x, w) - σ (j x, w)‖ := by simp [dist_eq_norm]
  rw [hpairdist, dist_eq_norm] at htransport
  have hsameρ := h₀ x hx (ρ (x, w) - x) hρsmall (by simpa using hC)
  simp only [add_sub_cancel] at hsameρ
  have hmismatch : ‖eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w))) -
      N (j x, σ (j x, w))‖ ≤ η * ‖w‖ := by
    calc
      _ ≤ ‖eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w))) - N (j x, ρ (x, w))‖ +
          ‖N (j x, ρ (x, w)) - N (j x, σ (j x, w))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ a * ‖ρ (x, w) - x‖ + (A : ℝ) * ‖ρ (x, w) - σ (j x, w)‖ :=
        add_le_add hsameρ.2.2 htransport
      _ ≤ a * (D * ‖w‖) + (A : ℝ) * (b * ‖w‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hρD ha.le)
          (mul_le_mul_of_nonneg_left hdiff A.coe_nonneg)
      _ = (η / 2 + (A : ℝ) * b) * ‖w‖ := by rw [← mul_assoc, haD]; ring
      _ ≤ η * ‖w‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

  have hcenterTube : (j x, x) ∈ cthickening δ Z :=
    self_subset_cthickening _ hcenterZ
  have hmodelDist := hA.dist_le_mul _ hσZ _ hcenterTube
  have hmodelPair : dist (j x, σ (j x, w)) (j x, x) = ‖σ (j x, w) - x‖ := by
    simp [dist_eq_norm]
  rw [hmodelPair, dist_eq_norm, hcenterN x hx] at hmodelDist
  have hmodelBound : ‖N (j x, σ (j x, w)) - eL.symm (x, fderiv ℝ G x)‖ ≤
      ((A : ℝ) * D) * ‖w‖ := by
    exact hmodelDist.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hσD A.coe_nonneg)
  refine ⟨hρdom, hσdom, hsource (eL.map_target (hlegal _ hC)), hσlegal,
    (hNspec _ hσlegal).2.1, ?_, ?_, ?_⟩
  · calc
      _ ≤ ‖eL.symm (ρ (x, w), fderiv ℝ G (ρ (x, w))) - N (j x, σ (j x, w))‖ +
          ‖N (j x, σ (j x, w)) - eL.symm (x, fderiv ℝ G x)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η * ‖w‖ + ((A : ℝ) * D) * ‖w‖ := add_le_add hmismatch hmodelBound
      _ ≤ (A₀ : ℝ) * ‖w‖ := by
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
        rw [hA₀]
        linarith only [hη1]
  · apply hmodelBound.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
    rw [hA₀]
    exact le_add_of_nonneg_right zero_le_one
  · exact hmismatch.trans (mul_le_mul_of_nonneg_right hηζ (norm_nonneg _))

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
