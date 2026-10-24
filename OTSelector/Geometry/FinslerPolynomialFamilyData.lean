import OTSelector.Geometry.FinslerPolynomialTubeData
import OTSelector.Geometry.Finsler.PotentialCompleteGauss
import OTSelector.Geometry.Finsler.CompleteTangentSmooth

/-!
# Actual normalized polynomial family data

The supplied inverse Legendre branch normalizes the polynomial covector to unit
speed. The same prescribed complete flow retains its exact initial momentum and
half energy at every time. Smooth level sections give a smooth tangent family and
Gauss orthogonality throughout that family, with no new flow selected.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Each legal polynomial covector determines its positive normalization, actual
initial position and momentum, and the same complete curve with half energy. -/
theorem polynomialPhaseFamily_seed_data (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (σ : ScalarSecondJet E × W → E) (j : ScalarSecondJet E) {w : W}
    (hlegal : (σ (j, w), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, w))) ∈ eL.target) :
    let q := (σ (j, w), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, w)))
    let z := F.covectorNormalization old eL (1 / 2) q
    let Γ := F.polynomialPhaseFamily old Φ eL σ j
    0 < F.covectorNormalizationScale old eL (1 / 2) q ∧
      z ∈ chartEnergyDomain old ∧ F.IsEulerLagrangeOn (Γ w) univ ∧
      Γ w 0 = (extChartAt 𝓘(ℝ, E) old).symm (σ (j, w)) ∧
      F.chartMomentumFamily old Γ (w, 0) =
        (σ (j, w), F.covectorNormalizationScale old eL (1 / 2) q • q.2) ∧
      ∀ t : ℝ, F.energy
        (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1 / 2 := by
  let q := (σ (j, w), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, w)))
  let z := F.covectorNormalization old eL (1 / 2) q
  let Γ := F.polynomialPhaseFamily old Φ eL σ j
  have hs := (hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)).2.2 q hlegal
  have hz : z ∈ chartEnergyDomain old := hs.2.1
  have hΓ : F.IsEulerLagrangeOn (Γ w) univ := hEL z hz
  have hi := hinit z hz
  refine ⟨hs.1, hz, hΓ, ?_, ?_, ?_⟩
  · have hb := congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1) hi
    rw [tangentChart_symm_eq old hz.1 z.2] at hb
    exact hb
  · have hm := hF.chartMomentum_of_tangent_eq (hΓ 0 (mem_univ _)) old hz hi
    exact hm.trans (Prod.ext rfl hs.2.2.2.1)
  · intro t
    calc
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) =
          F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨0, (1 : ℝ)⟩) := by
        unfold ContinuousFinslerNorm.energy
        rw [hF.speed_eq_of_isEulerLagrangeOn hΓ isPreconnected_univ
          (mem_univ t) (mem_univ 0)]
      _ = F.chartEnergy old z := congrArg F.energy hi
      _ = 1 / 2 := hs.2.2.1

variable [T2Space M]

/-- A smooth legal polynomial level section gives joint smoothness of the actual
prescribed family and its tangent at every time, without an extra flow hypothesis. -/
theorem polynomialPhaseFamily_contMDiff (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {σ : ScalarSecondJet E × W → E} {j : ScalarSecondJet E} {B : Set W}
    (hB : IsOpen B) (hσ : ContDiffOn ℝ ∞ (fun w ↦ σ (j, w)) B)
    (hlegal : ∀ w ∈ B,
      (σ (j, w), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, w))) ∈ eL.target) :
    let Γ := F.polynomialPhaseFamily old Φ eL σ j
    ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      ContMDiffOn 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) ∞ (fun q ↦ Γ q.1 q.2) (B ×ˢ univ) := by
  let q : W → E × (E →L[ℝ] ℝ) := fun w ↦
    (σ (j, w), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, w)))
  let seed : W → E × E := fun w ↦ F.covectorNormalization old eL (1 / 2) (q w)
  have hP : ContDiff ℝ ∞ (scalarSecondJetPolynomial j) :=
    contDiff_scalarSecondJetPolynomial_joint.comp (contDiff_const.prodMk contDiff_id)
  have hDP : ContDiff ℝ ∞ (fderiv ℝ (scalarSecondJetPolynomial j)) :=
    hP.fderiv_right (by simp)
  have hq : ContDiffOn ℝ ∞ q B := hσ.prodMk (hDP.comp_contDiffOn hσ)
  have hN := hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hseed : ContDiffOn ℝ ∞ seed B := hN.2.1.comp hq hlegal
  have hdomain : MapsTo seed B (chartEnergyDomain old) :=
    fun w hw ↦ (hN.2.2 (q w) (hlegal w hw)).2.1
  exact hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old hB
    (fun w hw ↦ hEL (seed w) (hdomain hw)) hseed hdomain
    (fun w hw ↦ hinit (seed w) (hdomain hw))

/-- Actual polynomial level labels remain Gauss-orthogonal to the momentum at every
time and in every legal chart of the same prescribed normalized family. -/
theorem polynomialPhaseFamily_gauss_zero (hF : F.IsSmoothStronglyConvex) (initial : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy initial))
    (hsource : eL.source ⊆ chartEnergyDomain initial)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {σ : ScalarSecondJet E × W → E} {j : ScalarSecondJet E} {B : Set W}
    (hB : IsOpen B) (hσ : ContDiffOn ℝ ∞ (fun w ↦ σ (j, w)) B)
    (hlegal : ∀ w ∈ B,
      (σ (j, w), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, w))) ∈ eL.target)
    {c : ℝ} (hlevel : ∀ w ∈ B, scalarSecondJetPolynomial j (σ (j, w)) = c)
    {w : W} (hw : w ∈ B) (old : M) (t : ℝ)
    (hx : F.polynomialPhaseFamily initial Φ eL σ j w t ∈
      (extChartAt 𝓘(ℝ, E) old).source) (ξ : W) :
    (F.chartMomentumFamily old (F.polynomialPhaseFamily initial Φ eL σ j) (w, t)).2
      (fderiv ℝ (fun b ↦ extChartAt 𝓘(ℝ, E) old
        (F.polynomialPhaseFamily initial Φ eL σ j b t)) w ξ) = 0 := by
  let Γ := F.polynomialPhaseFamily initial Φ eL σ j
  have hd (b : W) (hb : b ∈ B) :=
    hF.polynomialPhaseFamily_seed_data initial heL hsource hInv hEL hinit σ j (hlegal b hb)
  have hΓ : ∀ b ∈ B, F.IsEulerLagrangeOn (Γ b) univ := fun b hb ↦ (hd b hb).2.2.1
  have henergy : ∀ b ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ b) ⟨t, (1 : ℝ)⟩) = 1 / 2 :=
    fun b hb ↦ (hd b hb).2.2.2.2.2
  have hΓsmooth := (hF.polynomialPhaseFamily_contMDiff initial heL hsource hInv
    hEL hinit hB hσ hlegal).1
  have hx₀ : Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    dsimp only [Γ]
    rw [(hd w hw).2.2.2.1]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target (hd w hw).2.1.1
  have hP : ContDiff ℝ ∞ (scalarSecondJetPolynomial j) :=
    contDiff_scalarSecondJetPolynomial_joint.comp (contDiff_const.prodMk contDiff_id)
  apply hF.chartMomentumFamily_gauss_zero_of_potential_initial hB hΓ
    (hΓsmooth.of_le (by simp)) henergy initial 0
    (fun b hb ↦ (hd b hb).2.2.2.2.1) hw hx₀
    (hP.differentiable (by simp) _) ((hσ.contDiffAt (hB.mem_nhds hw)).differentiableAt
      (by simp)) (c := c) _ old t hx ξ
  filter_upwards [hB.mem_nhds hw] with b hb
  exact hlevel b hb

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
