import OTSelector.Geometry.FinslerPolynomialFamilyData

/-!
# Local legal data for the actual polynomial family

Legality of the central original covector extends to an open neighborhood of the
fixed labels. On that same neighborhood the explicit normalized velocity and scale
are smooth, have the original central values, and retain the actual conormal
momentum and half energy.
-/

open Set Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- A legal central original covector gives one open label neighborhood where all
actual polynomial seeds are legal and their normalized data are smooth and conormal. -/
theorem polynomialPhaseFamily_local_data (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} {x : E} {B : Set W}
    (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    {σ : ScalarSecondJet E × W → E}
    (hσ : ContDiffOn ℝ ∞
      (fun w ↦ σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), w)) B)
    (hσ₀ : σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), 0) = x)
    (hlegal : (x, fderiv ℝ G x) ∈ eL.target)
    (henergy : F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2) :
    let j : ScalarSecondJet E :=
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let P := scalarSecondJetPolynomial j
    let s : W → E := fun w ↦ σ (j, w)
    let q : W → E × (E →L[ℝ] ℝ) := fun w ↦ (s w, fderiv ℝ P (s w))
    let v : W → E := fun w ↦ (F.covectorNormalization old eL (1 / 2) (q w)).2
    let a : W → ℝ := fun w ↦ F.covectorNormalizationScale old eL (1 / 2) (q w)
    ∃ B' : Set W, IsOpen B' ∧ (0 : W) ∈ B' ∧ B' ⊆ B ∧
      (∀ w ∈ B', q w ∈ eL.target) ∧
      ContDiffOn ℝ ∞ v B' ∧ ContDiffOn ℝ ∞ a B' ∧ a 0 = 1 ∧
      (s 0, v 0) = eL.symm (x, fderiv ℝ G x) ∧
      ∀ w ∈ B', 0 < a w ∧ (s w, v w) ∈ chartEnergyDomain old ∧
        F.chartEnergy old (s w, v w) = 1 / 2 ∧
        parametricLegendre (F.chartEnergy old) (s w, v w) =
          potentialConormalState P s a w := by
  let j : ScalarSecondJet E :=
    (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let P := scalarSecondJetPolynomial j
  let s : W → E := fun w ↦ σ (j, w)
  let q : W → E × (E →L[ℝ] ℝ) := fun w ↦ (s w, fderiv ℝ P (s w))
  let v : W → E := fun w ↦ (F.covectorNormalization old eL (1 / 2) (q w)).2
  let a : W → ℝ := fun w ↦ F.covectorNormalizationScale old eL (1 / 2) (q w)
  have hP : ContDiff ℝ ∞ P :=
    contDiff_scalarSecondJetPolynomial_joint.comp (contDiff_const.prodMk contDiff_id)
  have hDP : ContDiff ℝ ∞ (fderiv ℝ P) := hP.fderiv_right (by simp)
  have hq : ContDiffOn ℝ ∞ q B := hσ.prodMk (hDP.comp_contDiffOn hσ)
  have hq₀ : q 0 = (x, fderiv ℝ G x) := by
    change (s 0, fderiv ℝ P (s 0)) = _
    rw [show s 0 = x from hσ₀]
    exact Prod.ext rfl (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv
  let B' := B ∩ q ⁻¹' eL.target
  have hB' : IsOpen B' := hq.continuousOn.isOpen_inter_preimage hB eL.open_target
  have h0B' : (0 : W) ∈ B' := ⟨h0B, by
    change q 0 ∈ eL.target
    rw [hq₀]
    exact hlegal⟩
  have hsub : B' ⊆ B := inter_subset_left
  have hqlegal : MapsTo q B' eL.target := fun _ hw ↦ hw.2
  obtain ⟨hscale, hnormal, hspec⟩ := hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨B', hB', h0B', hsub, fun w hw ↦ hqlegal hw,
    (hnormal.comp (hq.mono hsub) hqlegal).snd,
    hscale.comp (hq.mono hsub) hqlegal, ?_, ?_, ?_⟩
  · change Real.sqrt ((1 / 2) / F.chartEnergy old (eL.symm (q 0))) = 1
    rw [hq₀, henergy]
    norm_num
  · change F.covectorNormalization old eL (1 / 2) (q 0) = _
    rw [hq₀]
    exact (hspec _ hlegal).2.2.2.2 henergy
  · intro w hw
    have hd := hspec (q w) (hqlegal hw)
    exact ⟨hd.1, hd.2.1, hd.2.2.1, Prod.ext rfl hd.2.2.2.1⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
