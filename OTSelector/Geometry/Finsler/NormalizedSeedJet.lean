import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Symplectic.PotentialConormal

/-!
# Geometry.Finsler.NormalizedSeedJet

* **Conditions:** A genuinely constructed constant-energy conormal seed with the actual first-order eikonal identity at the base point.
* **Objects:** Zero derivative of the same normalization scalar and the exact original conormal/initial-momentum first jet.
* **Proof detail:** Differentiate both actual energy identities, divide by positive radial pairing and apply the product chain rule to the already chosen scalar.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerNormalizedSeedJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerNormalizedSeedJet`; the selected original proof blocks follow. -/
section

/-!
# First jets of the constructed constant-energy conormal seed

The scalar already used by a genuine Finsler normal family has zero derivative when
the unscaled covector graph satisfies the first-order eikonal identity. This follows
from the two actual energy derivatives and positive original radial pairing, without
requiring an explicit formula for the scalar or constructing a second normalization.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The scalar of any actual constant-energy normal seed has zero derivative at a
center where the unscaled original Hamiltonian graph has zero derivative. The inverse
branch only needs to contain the common center, not the entire supplied family. -/
theorem fderiv_normalScale_eq_zero (hF : F.IsSmoothStronglyConvex) (old : M)
    {σ v : W → E} {q : W → E →L[ℝ] ℝ} {a : W → ℝ} {w₀ : W}
    (hσ : DifferentiableAt ℝ σ w₀) (hv : ContinuousAt v w₀)
    (hq : DifferentiableAt ℝ q w₀) (ha : DifferentiableAt ℝ a w₀) (ha₀ : a w₀ = 1)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hsource : e.source ⊆ chartEnergyDomain old)
    (hG : ContDiffOn ℝ ∞ e.symm e.target) (hzs : (σ w₀, v w₀) ∈ e.source)
    (hdata : ∀ᶠ w in 𝓝 w₀,
      F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ w₀, v w₀) ∧
      fiberLegendre (F.chartEnergy old) (σ w, v w) = a w • q w)
    (hjet : HasFDerivAt
      (fun w ↦ localHamiltonian (F.chartEnergy old) e (σ w, q w)) (0 : W →L[ℝ] ℝ) w₀) :
    fderiv ℝ a w₀ = 0 := by
  let L := F.chartEnergy old
  let H := localHamiltonian L e
  let z := (σ w₀, v w₀)
  let p := (σ w₀, q w₀)
  have hm : fiberLegendre L z = q w₀ := by
    simpa only [L, z, ha₀, one_smul] using hdata.self_of_nhds.2
  have hep : e z = p := by
    rw [he]
    exact Prod.ext rfl hm
  have hpt : p ∈ e.target := hep ▸ e.map_source hzs
  have hinv : e.symm p = z := by rw [← hep, e.left_inv hzs]
  have hLi : DifferentiableAt ℝ L (e.symm p) :=
    ((hF.contDiffOn_chartEnergy old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds (hsource (e.map_target hpt)))).differentiableAt
        (by simp)
  have hGi := (hG.contDiffAt (e.open_target.mem_nhds hpt)).differentiableAt (by simp)
  have hHd : DifferentiableAt ℝ H p :=
    ((contDiffOn_localHamiltonian ((hF.contDiffOn_chartEnergy old).mono hsource) hG).contDiffAt
      (e.open_target.mem_nhds hpt)).differentiableAt (by simp)
  have hnear : ∀ᶠ w in 𝓝 w₀, (σ w, v w) ∈ e.source :=
    (hσ.continuousAt.prodMk hv).preimage_mem_nhds (e.open_source.mem_nhds hzs)
  have hconst : (fun w ↦ H (σ w, a w • q w)) =ᶠ[𝓝 w₀] fun _ ↦ L z := by
    filter_upwards [hnear, hdata] with w hw hd
    have hepw : e (σ w, v w) = (σ w, a w • q w) := by
      rw [he]
      exact Prod.ext rfl hd.2
    rw [← hepw]
    change localHamiltonian (F.chartEnergy old) e (e (σ w, v w)) = _
    rw [hF.localHamiltonian_chartEnergy_eq old he hsource (e.map_source hw), e.left_inv hw]
    exact hd.1
  have hscaled : HasFDerivAt (fun w ↦ H (σ w, a w • q w))
      ((fderiv ℝ H p).comp ((fderiv ℝ σ w₀).prod
        (a w₀ • fderiv ℝ q w₀ + (fderiv ℝ a w₀).smulRight (q w₀)))) w₀ := by
    have hh : DifferentiableAt ℝ H (σ w₀, a w₀ • q w₀) := by
      simpa only [ha₀, one_smul] using hHd
    simpa only [p, ha₀, one_smul, Function.comp_apply, Pi.smul_apply] using!
      hh.hasFDerivAt.comp w₀ (hσ.hasFDerivAt.prodMk (ha.hasFDerivAt.smul hq.hasFDerivAt))
  have hscaledZero := hscaled.unique
    ((hasFDerivAt_const (𝕜 := ℝ) (L z) w₀).congr_of_eventuallyEq hconst)
  have hunc : HasFDerivAt (fun w ↦ H (σ w, q w))
      ((fderiv ℝ H p).comp ((fderiv ℝ σ w₀).prod (fderiv ℝ q w₀))) w₀ := by
    simpa only [Function.comp_apply] using!
      hHd.hasFDerivAt.comp w₀ (hσ.hasFDerivAt.prodMk hq.hasFDerivAt)
  have hunscaled := hunc.unique hjet
  have hrad : q w₀ (v w₀) ≠ 0 := by
    rw [← hm, hF.chartEnergy_euler old (hsource hzs)]
    exact (mul_pos (by norm_num) (F.chartEnergy_pos old (hsource hzs))).ne'
  ext u
  have hs := congrArg (fun A : W →L[ℝ] ℝ ↦ A u) hscaledZero
  have hu := congrArg (fun A : W →L[ℝ] ℝ ↦ A u) hunscaled
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ha₀, one_smul, _root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.zero_apply] at hs hu
  rw [localHamiltonian_fderiv_apply he hpt hLi hGi, hinv] at hs hu
  simp only [z, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul] at hs hu
  have hz : fderiv ℝ a w₀ u * q w₀ (v w₀) = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_right hrad

/-- The already constructed potential conormal has the unscaled first jet. Its scale
has zero derivative as a consequence of original constant energy and the eikonal jet. -/
theorem potentialConormalState_firstJet_of_constantEnergy
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {f : E → ℝ} {σ v : W → E} {a : W → ℝ} {w₀ : W}
    (hf : ContDiffAt ℝ 2 f (σ w₀)) (hσ : DifferentiableAt ℝ σ w₀)
    (hv : ContinuousAt v w₀) (ha : DifferentiableAt ℝ a w₀) (ha₀ : a w₀ = 1)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hsource : e.source ⊆ chartEnergyDomain old)
    (hG : ContDiffOn ℝ ∞ e.symm e.target) (hzs : (σ w₀, v w₀) ∈ e.source)
    (hdata : ∀ᶠ w in 𝓝 w₀,
      F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ w₀, v w₀) ∧
      fiberLegendre (F.chartEnergy old) (σ w, v w) = a w • fderiv ℝ f (σ w))
    (hjet : HasFDerivAt (fun w ↦ localHamiltonian (F.chartEnergy old) e
      (σ w, fderiv ℝ f (σ w))) (0 : W →L[ℝ] ℝ) w₀) :
    fderiv ℝ a w₀ = 0 ∧
      HasFDerivAt (potentialConormalState f σ a)
        ((fderiv ℝ σ w₀).prod
          ((fderiv ℝ (fderiv ℝ f) (σ w₀)).comp (fderiv ℝ σ w₀))) w₀ := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hq : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f (σ w)) w₀ := hdf.comp w₀ hσ
  have hazero := hF.fderiv_normalScale_eq_zero old hσ hv hq ha ha₀ he hsource hG hzs
    hdata hjet
  refine ⟨hazero, ?_⟩
  simpa only [ha₀, one_smul, hazero, ContinuousLinearMap.zero_smulRight, add_zero] using
    hasFDerivAt_potentialConormalState hf hσ ha

/-- The same constructed family has the unscaled potential first jet in its actual
initial chart momentum. The nearby equality is exactly the initial-momentum conclusion
of `exists_complete_potentialFamily`, restricted to its open parameter neighborhood. -/
theorem initialMomentum_firstJet_of_constantEnergy
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {f : E → ℝ} {σ v : W → E} {a : W → ℝ} {w₀ : W}
    (hf : ContDiffAt ℝ 2 f (σ w₀)) (hσ : DifferentiableAt ℝ σ w₀)
    (hv : ContinuousAt v w₀) (ha : DifferentiableAt ℝ a w₀) (ha₀ : a w₀ = 1)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hsource : e.source ⊆ chartEnergyDomain old)
    (hG : ContDiffOn ℝ ∞ e.symm e.target) (hzs : (σ w₀, v w₀) ∈ e.source)
    (hdata : ∀ᶠ w in 𝓝 w₀,
      F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ w₀, v w₀) ∧
      fiberLegendre (F.chartEnergy old) (σ w, v w) = a w • fderiv ℝ f (σ w))
    (hjet : HasFDerivAt (fun w ↦ localHamiltonian (F.chartEnergy old) e
      (σ w, fderiv ℝ f (σ w))) (0 : W →L[ℝ] ℝ) w₀)
    {Γ : W → ℝ → M} {t₀ : ℝ}
    (hmomentum : (fun w ↦ F.chartMomentumFamily old Γ (w, t₀)) =ᶠ[𝓝 w₀]
      potentialConormalState f σ a) :
    fderiv ℝ a w₀ = 0 ∧
      HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, t₀))
        ((fderiv ℝ σ w₀).prod
          ((fderiv ℝ (fderiv ℝ f) (σ w₀)).comp (fderiv ℝ σ w₀))) w₀ := by
  obtain ⟨ha, hseed⟩ := hF.potentialConormalState_firstJet_of_constantEnergy old hf hσ hv
    ha ha₀ he hsource hG hzs hdata hjet
  exact ⟨ha, hseed.congr_of_eventuallyEq hmomentum⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
