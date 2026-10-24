import OTSelector.Analysis.Calculus.IntrinsicCostCoefficientPullback
import OTSelector.Analysis.Calculus.SecondJetPolynomial
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Calibration.PotentialNormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.NormalizedSeedJet
import OTSelector.Geometry.Manifold.SmoothLevelChart
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerIntrinsicCostCoefficientNormalSeed.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerIntrinsicCostCoefficientNormalSeed`; the selected original proof blocks follow. -/
section

/-!
Conditions: A regular smooth level section with prescribed tangent map and an actual isotropic energy-tangent phase jet.

Objects: A smooth polynomial normal seed whose normalized phase has the same first jet.

Proof detail: Extend the symmetric tangential jet, construct a polynomial potential, take its level chart and normalize Legendre energy at one-half.

Sources: Ana Cannas da Silva, Section 3.2, pp. 16–17; Section 3.3, Definition 3.5, Proposition 3.6 and Corollary 3.7, pp. 17–18 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=24); Hassler Whitney, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2); Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); Matias Dahl, Section 7, Definition 7.3 and Proposition 7.4, p. 31; Section 7.2, Propositions 7.14–7.15, p. 35 (https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=31).
Relation: Finite-jet normal-seed construction from classical conormal/jet/normalization tools; the exact assembly is locally proved.
-/

/-!
# Smooth normal seeds realizing an actual isotropic label jet

A symmetric extension of the actual pulled-back covector derivative gives a smooth
potential. Its true level section retains the original label derivative. The same
Legendre branch normalizes its covectors while preserving the initial phase jet.
-/

open Set Filter Manifold Module
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A smooth potential has a local level section in the supplied labels with any
prescribed derivative annihilated by its nonzero differential. -/
theorem exists_smooth_levelSection_prescribed_derivative
    {P : E → ℝ} (hP : ContDiff ℝ ∞ P) (x : E)
    (hp : fderiv ℝ P x ≠ 0) (R : W →L[ℝ] E)
    (hnormal : ∀ ξ, fderiv ℝ P x (R ξ) = 0) :
    ∃ (B : Set W) (σ : W → E), IsOpen B ∧ 0 ∈ B ∧
      ContDiffOn ℝ ∞ σ B ∧ σ 0 = x ∧
      (∀ w ∈ B, P (σ w) = P x) ∧ HasFDerivAt σ R 0 := by
  let p := fderiv ℝ P x
  let A : W →L[ℝ] p.ker := R.codRestrict p.ker (fun ξ ↦ hnormal ξ)
  obtain ⟨V, s, U, hV, h0, hs, hs0, _, hlevel, hD, _⟩ :=
    exists_smooth_levelChart isOpen_univ hP.contDiffOn (mem_univ x) hp
  let B := A ⁻¹' V
  have h0B : (0 : W) ∈ B := by simpa only [B, mem_preimage, map_zero] using h0
  refine ⟨B, s ∘ A, hV.preimage A.continuous, h0B,
    hs.comp A.contDiff.contDiffOn (fun _ hw ↦ hw), ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, map_zero] using hs0
  · intro w hw
    exact hlevel (A w) hw
  · have hd : HasFDerivAt s p.ker.subtypeL (A 0) := by simpa only [map_zero] using hD
    simpa only [ContinuousLinearMap.subtypeL_comp_codRestrict] using!
      hd.comp 0 A.hasFDerivAt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- A supplied actual energy-tangent isotropic normal phase jet produces one smooth
potential level seed, normalized on the same genuine inverse branch, with its exact jet. -/
theorem exists_normalPotentialSeed_same_phaseJet
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : E × E → E × (E →L[ℝ] ℝ)) = parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {z₀ : E × (E →L[ℝ] ℝ)} (hz₀ : z₀ ∈ e.target)
    (henergy : localHamiltonian (F.chartEnergy old) e z₀ = (1 / 2 : ℝ))
    (R : W →L[ℝ] E) (Q : W →L[ℝ] E →L[ℝ] ℝ)
    (hzero : (fderiv ℝ (localHamiltonian (F.chartEnergy old) e) z₀).comp
      (R.prod Q) = 0)
    (hR : Function.Injective R) (hisotropic : ∀ ξ η : W, Q ξ (R η) = Q η (R ξ))
    (hnormal : ∀ ξ : W, z₀.2 (R ξ) = 0) (value : ℝ) :
    ∃ (H : E →L[ℝ] E →L[ℝ] ℝ) (B : Set W)
      (σ v : W → E) (a : W → ℝ),
      (∀ x y, H x y = H y x) ∧ H.comp R = Q ∧
      IsOpen B ∧ 0 ∈ B ∧ ContDiffOn ℝ ∞ σ B ∧ ContDiffOn ℝ ∞ v B ∧
      ContDiffOn ℝ ∞ a B ∧ σ 0 = z₀.1 ∧ HasFDerivAt σ R 0 ∧
      v 0 = (e.symm z₀).2 ∧ a 0 = 1 ∧ fderiv ℝ a 0 = 0 ∧
      (∀ w ∈ B, secondJetPolynomial z₀.1 value z₀.2 H (σ w) = value) ∧
      (∀ w ∈ B, (σ w, v w) ∈ e.source ∧ 0 < a w ∧
        F.chartEnergy old (σ w, v w) = (1 / 2 : ℝ) ∧
        fiberLegendre (F.chartEnergy old) (σ w, v w) =
          a w • fderiv ℝ (secondJetPolynomial z₀.1 value z₀.2 H) (σ w) ∧
        e.symm (σ w, a w • fderiv ℝ (secondJetPolynomial z₀.1 value z₀.2 H) (σ w)) =
          (σ w, v w)) ∧
      HasFDerivAt (fun w ↦ (σ w,
        a w • fderiv ℝ (secondJetPolynomial z₀.1 value z₀.2 H) (σ w))) (R.prod Q) 0 := by
  obtain ⟨H, hsym, hcomp⟩ := exists_symmetric_phase_extension R Q hR hisotropic
  let P := secondJetPolynomial z₀.1 value z₀.2 H
  have hP : ContDiff ℝ ∞ P := contDiff_secondJetPolynomial _ _ _ _
  have hDP : HasFDerivAt P z₀.2 z₀.1 := by
    have hd := hasFDerivAt_secondJetPolynomial z₀.1 value z₀.2 H hsym z₀.1
    rw [sub_self, H.map_zero, add_zero] at hd
    exact hd
  have hH : HasFDerivAt (fderiv ℝ P) H z₀.1 :=
    hasFDerivAt_fderiv_secondJetPolynomial _ _ _ _ hsym _
  have hlegal := hsub (e.map_target hz₀)
  have hpv : z₀.2 (e.symm z₀).2 ≠ 0 := by
    have hh := hF.chartLegendre_self_eq_chartLength_sq old hlegal
    rw [(parametricLegendre_inverse_components he hz₀).2] at hh
    rw [hh]
    exact pow_ne_zero _ (NNReal.coe_pos.mpr (F.chartLength_pos old hlegal)).ne'
  have hp : fderiv ℝ P z₀.1 ≠ 0 := by
    rw [hDP.fderiv]
    intro h
    exact hpv (by rw [h]; rfl)
  obtain ⟨B, σ, hB, h0, hσ, hσ0, hlevel, hσD⟩ :=
    exists_smooth_levelSection_prescribed_derivative hP z₀.1 hp R
      (fun ξ ↦ by rw [hDP.fderiv]; exact hnormal ξ)
  let q : W → E →L[ℝ] ℝ := fun w ↦ fderiv ℝ P (σ w)
  have hq : ContDiffOn ℝ ∞ q B := (hP.fderiv_right (by simp)).comp_contDiffOn hσ
  have hq0 : q 0 = z₀.2 := by change fderiv ℝ P (σ 0) = _; rw [hσ0, hDP.fderiv]
  have hqD : HasFDerivAt q Q 0 := by
    have hd : HasFDerivAt (fderiv ℝ P) H (σ 0) := by rw [hσ0]; exact hH
    simpa only [hcomp] using! hd.comp 0 hσD
  have hcenter : (σ 0, (e.symm z₀).2) = e.symm z₀ :=
    Prod.ext (hσ0.trans (parametricLegendre_inverse_components he hz₀).1.symm) rfl
  have hzs : (σ 0, (e.symm z₀).2) ∈ e.source := hcenter ▸ e.map_target hz₀
  have hm : q 0 = fiberLegendre (F.chartEnergy old) (σ 0, (e.symm z₀).2) := by
    rw [hcenter, hq0]
    exact (parametricLegendre_inverse_components he hz₀).2.symm
  have hE : F.chartEnergy old (σ 0, (e.symm z₀).2) = (1 / 2 : ℝ) := by
    rw [hcenter, ← hF.localHamiltonian_chartEnergy_eq old he hsub hz₀]
    exact henergy
  obtain ⟨U, v, a, hU, h0U, hUB, hv, ha, hv0, ha0, hd⟩ :=
    hF.exists_constantEnergy_covectorData_on_branch old hB h0 hσ hq he hzs hsub hi hm
  have hjet : HasFDerivAt (fun w ↦ localHamiltonian (F.chartEnergy old) e (σ w, q w))
      (0 : W →L[ℝ] ℝ) 0 := by
    have hHam := ((contDiffOn_localHamiltonian
      ((hF.contDiffOn_chartEnergy old).mono hsub) hi).contDiffAt
      (e.open_target.mem_nhds hz₀)).differentiableAt (by simp)
    have hHam' : HasFDerivAt (localHamiltonian (F.chartEnergy old) e)
        (fderiv ℝ (localHamiltonian (F.chartEnergy old) e) z₀) (σ 0, q 0) := by
      simpa only [hσ0, hq0, Prod.mk.eta] using hHam.hasFDerivAt
    simpa only [hzero] using! hHam'.comp 0 (hσD.prodMk hqD)
  have hnear : ∀ᶠ w in 𝓝 (0 : W),
      F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ 0, v 0) ∧
      fiberLegendre (F.chartEnergy old) (σ w, v w) = a w • q w := by
    filter_upwards [hU.mem_nhds h0U] with w hw
    exact ⟨(hd w hw).2.2.1.trans (by rw [hv0]), (hd w hw).2.2.2.1⟩
  have haD := (ha.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
  have haZero := hF.fderiv_normalScale_eq_zero old hσD.differentiableAt
    (hv.contDiffAt (hU.mem_nhds h0U)).continuousAt hqD.differentiableAt haD ha0
    he hsub hi (by rw [hv0]; exact hzs) hnear hjet
  refine ⟨H, U, σ, v, a, hsym, hcomp, hU, h0U, hσ.mono hUB, hv, ha,
    hσ0, hσD, hv0, ha0, haZero, ?_, ?_, ?_⟩
  · intro w hw
    exact (hlevel w (hUB hw)).trans (secondJetPolynomial_self _ _ _ _)
  · intro w hw
    exact ⟨(hd w hw).1, (hd w hw).2.1, (hd w hw).2.2.1.trans hE,
      (hd w hw).2.2.2⟩
  · simpa only [ha0, haZero, one_smul, ContinuousLinearMap.zero_smulRight, add_zero,
      Pi.smul_apply] using! hσD.prodMk (haD.hasFDerivAt.smul hqD)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
