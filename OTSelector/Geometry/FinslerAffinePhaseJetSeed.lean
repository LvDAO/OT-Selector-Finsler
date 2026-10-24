import OTSelector.Geometry.Finsler.Calibration.PotentialNormalData
import OTSelector.Geometry.Finsler.NormalizedSeedJet

/-!
# Constant-energy smooth seeds with a prescribed energy-tangent phase jet

An affine position-covector seed is normalized on the supplied original Legendre branch.
At an energy-tangent jet the already constructed positive scale has zero derivative,
so normalization preserves the complete position-covector first jet.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Normalize the affine phase with its exact prescribed jet. All nearby seeds have
original energy one half, and the scale has value one and derivative zero at the center. -/
theorem exists_affinePhase_constantEnergy_same_firstJet
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : E × E → E × (E →L[ℝ] ℝ)) = parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {z₀ : E × (E →L[ℝ] ℝ)} (hz₀ : z₀ ∈ e.target)
    (henergy : localHamiltonian (F.chartEnergy old) e z₀ = (1 / 2 : ℝ))
    (R : W →L[ℝ] E) (Q : W →L[ℝ] E →L[ℝ] ℝ)
    (hzero : (fderiv ℝ (localHamiltonian (F.chartEnergy old) e) z₀).comp
      (R.prod Q) = 0) :
    let σ : W → E := fun w ↦ z₀.1 + R w
    let q : W → E →L[ℝ] ℝ := fun w ↦ z₀.2 + Q w
    ∃ (U : Set W) (v : W → E) (a : W → ℝ),
      IsOpen U ∧ 0 ∈ U ∧ ContDiffOn ℝ ∞ v U ∧ ContDiffOn ℝ ∞ a U ∧
      v 0 = (e.symm z₀).2 ∧ a 0 = 1 ∧ fderiv ℝ a 0 = 0 ∧
      (∀ w ∈ U, (σ w, v w) ∈ e.source ∧ 0 < a w ∧
        F.chartEnergy old (σ w, v w) = (1 / 2 : ℝ) ∧
        fiberLegendre (F.chartEnergy old) (σ w, v w) = a w • q w ∧
        e.symm (σ w, a w • q w) = (σ w, v w)) ∧
      HasFDerivAt (fun w ↦ (σ w, a w • q w)) (R.prod Q) 0 := by
  let σ : W → E := fun w ↦ z₀.1 + R w
  let q : W → E →L[ℝ] ℝ := fun w ↦ z₀.2 + Q w
  have hσ : ContDiff ℝ ∞ σ := contDiff_const.add R.contDiff
  have hq : ContDiff ℝ ∞ q := contDiff_const.add Q.contDiff
  have hσ₀ : σ 0 = z₀.1 := by simp [σ]
  have hq₀ : q 0 = z₀.2 := by simp [q]
  have hσD : HasFDerivAt σ R 0 := (R.hasFDerivAt).const_add z₀.1
  have hqD : HasFDerivAt q Q 0 := (Q.hasFDerivAt).const_add z₀.2
  have hcenter : (σ 0, (e.symm z₀).2) = e.symm z₀ := by
    exact Prod.ext (hσ₀.trans (parametricLegendre_inverse_components he hz₀).1.symm) rfl
  have hzs : (σ 0, (e.symm z₀).2) ∈ e.source := hcenter ▸ e.map_target hz₀
  have hm : q 0 = fiberLegendre (F.chartEnergy old) (σ 0, (e.symm z₀).2) := by
    rw [hcenter, hq₀]
    exact (parametricLegendre_inverse_components he hz₀).2.symm
  have hE : F.chartEnergy old (σ 0, (e.symm z₀).2) = (1 / 2 : ℝ) := by
    rw [hcenter, ← hF.localHamiltonian_chartEnergy_eq old he hsub hz₀]
    exact henergy
  obtain ⟨U, v, a, hU, h0, _, hv, ha, hv0, ha0, hd⟩ :=
    hF.exists_constantEnergy_covectorData_on_branch old isOpen_univ (mem_univ (0 : W))
      hσ.contDiffOn hq.contDiffOn he hzs hsub hi hm
  have hjet : HasFDerivAt (fun w ↦ localHamiltonian (F.chartEnergy old) e (σ w, q w))
      (0 : W →L[ℝ] ℝ) 0 := by
    have hH := ((contDiffOn_localHamiltonian
      ((hF.contDiffOn_chartEnergy old).mono hsub) hi).contDiffAt
      (e.open_target.mem_nhds hz₀)).differentiableAt (by simp)
    have hH' : HasFDerivAt (localHamiltonian (F.chartEnergy old) e)
        (fderiv ℝ (localHamiltonian (F.chartEnergy old) e) z₀) (σ 0, q 0) := by
      simpa only [hσ₀, hq₀, Prod.mk.eta] using hH.hasFDerivAt
    simpa only [hzero] using! hH'.comp 0 (hσD.prodMk hqD)
  have hnear : ∀ᶠ w in 𝓝 (0 : W),
      F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ 0, v 0) ∧
      fiberLegendre (F.chartEnergy old) (σ w, v w) = a w • q w := by
    filter_upwards [hU.mem_nhds h0] with w hw
    exact ⟨(hd w hw).2.2.1.trans (by rw [hv0]), (hd w hw).2.2.2.1⟩
  have haD := (ha.contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)
  have haZero := hF.fderiv_normalScale_eq_zero old hσD.differentiableAt
    (hv.contDiffAt (hU.mem_nhds h0)).continuousAt hqD.differentiableAt haD ha0
    he hsub hi (by rw [hv0]; exact hzs) hnear hjet
  refine ⟨U, v, a, hU, h0, hv, ha, hv0, ha0, haZero, ?_, ?_⟩
  · intro w hw
    exact ⟨(hd w hw).1, (hd w hw).2.1, (hd w hw).2.2.1.trans hE,
      (hd w hw).2.2.2⟩
  · simpa only [ha0, haZero, one_smul, ContinuousLinearMap.zero_smulRight, add_zero, Pi.smul_apply] using!
      hσD.prodMk (haD.hasFDerivAt.smul hqD)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
