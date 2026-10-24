import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialNormalData.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialNormalData`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.PotentialNormalData

* **Conditions:** A smooth position/covector parameterization through a true nonzero Finsler Legendre state, with one supplied genuine inverse branch for the branchwise theorem.
* **Objects:** A positive smooth constant-energy normalization of the varying actual covector field, preserving the same inverse branch after restriction.
* **Proof detail:** Invert the original covector, scale by a positive square root of the energy ratio, and shrink the open parameter set by continuity to retain branch membership.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Constant-energy normalization of a genuine varying conormal field

A smooth covector field along any smooth position parameterization is inverted using a
genuine local Legendre chart. Positive square-root scaling normalizes the original energy.
Both the unscaled and scaled states remain in the same inverse branch after restriction
to a constructed open neighborhood. For a potential, the covector field is its actual
differential along the parameterization, with no fixed-direction replacement.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Normalize any smooth varying covector field on the supplied genuine inverse branch.
The positive scale, constant actual energy and same-branch inverse identity are constructed. -/
theorem exists_constantEnergy_covectorData_on_branch (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {σ : W → E} {q : W → E →L[ℝ] ℝ} {V : Set W} {w₀ : W}
    (hV : IsOpen V) (hw₀ : w₀ ∈ V)
    (hσ : ContDiffOn ℝ ∞ σ V) (hq : ContDiffOn ℝ ∞ q V)
    {v₀ : E}
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hzs : (σ w₀, v₀) ∈ e.source) (hsub : e.source ⊆ chartEnergyDomain x₀)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    (hmatch : q w₀ = fiberLegendre (F.chartEnergy x₀) (σ w₀, v₀)) :
    ∃ (U : Set W) (v : W → E) (a : W → ℝ),
      IsOpen U ∧ w₀ ∈ U ∧ U ⊆ V ∧
      ContDiffOn ℝ ∞ v U ∧ ContDiffOn ℝ ∞ a U ∧ v w₀ = v₀ ∧ a w₀ = 1 ∧
      ∀ w ∈ U, (σ w, v w) ∈ e.source ∧ 0 < a w ∧
        F.chartEnergy x₀ (σ w, v w) = F.chartEnergy x₀ (σ w₀, v₀) ∧
        fiberLegendre (F.chartEnergy x₀) (σ w, v w) = a w • q w ∧
        e.symm (σ w, a w • q w) = (σ w, v w) := by
  let L := F.chartEnergy x₀
  let z := (σ w₀, v₀)
  let U₀ := V ∩ (fun w ↦ (σ w, q w)) ⁻¹' e.target
  let b : W → E := fun w ↦ (e.symm (σ w, q w)).2
  have hU₀ : IsOpen U₀ :=
    (hσ.prodMk hq).continuousOn.isOpen_inter_preimage hV e.open_target
  have hcenter : (σ w₀, q w₀) = parametricLegendre L z := Prod.ext rfl hmatch
  have hwU₀ : w₀ ∈ U₀ := ⟨hw₀, by
    change (σ w₀, q w₀) ∈ e.target
    rw [hcenter, ← he]
    exact e.map_source hzs⟩
  have hmem (w : W) (hw : w ∈ U₀) : (σ w, b w) ∈ chartEnergyDomain x₀ := by
    have hc := parametricLegendre_inverse_components he hw.2
    have h := hsub (e.map_target hw.2)
    have heq : e.symm (σ w, q w) = (σ w, b w) := Prod.ext hc.1 rfl
    rwa [heq] at h
  have hb : ContDiffOn ℝ ∞ b U₀ :=
    (hG.comp ((hσ.prodMk hq).mono inter_subset_left) (fun _ hw ↦ hw.2)).snd
  have hb₀ : b w₀ = v₀ := by
    change (e.symm (σ w₀, q w₀)).2 = v₀
    rw [hcenter, ← he, e.left_inv hzs]
  have hmom (w : W) (hw : w ∈ U₀) : fiberLegendre L (σ w, b w) = q w := by
    have hc := parametricLegendre_inverse_components he hw.2
    have heq : e.symm (σ w, q w) = (σ w, b w) := Prod.ext hc.1 rfl
    simpa only [heq] using hc.2
  have henergy : ContDiffOn ℝ ∞ (fun w ↦ L (σ w, b w)) U₀ :=
    (hF.contDiffOn_chartEnergy x₀).comp ((hσ.mono inter_subset_left).prodMk hb) hmem
  have hpos (w : W) (hw : w ∈ U₀) : 0 < L (σ w, b w) :=
    F.chartEnergy_pos x₀ (hmem w hw)
  have hzpos : 0 < L z := F.chartEnergy_pos x₀ (hsub hzs)
  let a : W → ℝ := fun w ↦ Real.sqrt (L z / L (σ w, b w))
  have ha : ContDiffOn ℝ ∞ a U₀ :=
    (contDiffOn_const.div henergy (fun w hw ↦ (hpos w hw).ne')).sqrt
      (fun w hw ↦ (div_pos hzpos (hpos w hw)).ne')
  have ha_pos (w : W) (hw : w ∈ U₀) : 0 < a w :=
    Real.sqrt_pos.2 (div_pos hzpos (hpos w hw))
  have ha₀ : a w₀ = 1 := by
    dsimp only [a]
    rw [hb₀, div_self hzpos.ne', Real.sqrt_one]
  let v : W → E := fun w ↦ a w • b w
  have hv : ContDiffOn ℝ ∞ v U₀ := ha.smul hb
  have hv₀ : v w₀ = v₀ := by simp only [v, ha₀, one_smul, hb₀]
  let U := U₀ ∩ (fun w ↦ (σ w, v w)) ⁻¹' e.source
  have hU : IsOpen U :=
    ((hσ.mono inter_subset_left).prodMk hv).continuousOn.isOpen_inter_preimage hU₀ e.open_source
  have hwU : w₀ ∈ U := ⟨hwU₀, by change (σ w₀, v w₀) ∈ e.source; rwa [hv₀]⟩
  refine ⟨U, v, a, hU, hwU, fun _ hw ↦ hw.1.1,
    hv.mono inter_subset_left, ha.mono inter_subset_left, hv₀, ha₀, ?_⟩
  intro w hw
  have hm := hmem w hw.1
  have hap := ha_pos w hw.1
  have hmomentum : fiberLegendre L (σ w, v w) = a w • q w := by
    dsimp only [v]
    rw [hF.chartLegendre_pos_smul x₀ hm.1 hm.2 hap, hmom w hw.1]
  refine ⟨hw.2, hap, ?_, hmomentum, ?_⟩
  · dsimp only [v]
    rw [F.chartEnergy_smul x₀ hm.1]
    change (Real.sqrt (L z / L (σ w, b w))) ^ 2 * L (σ w, b w) = L z
    rw [Real.sq_sqrt (div_pos hzpos (hpos w hw.1)).le]
    exact div_mul_cancel₀ _ (hpos w hw.1).ne'
  · rw [← hmomentum]
    change e.symm (parametricLegendre L (σ w, v w)) = (σ w, v w)
    rw [← he, e.left_inv hw.2]

/-- Original Finsler data normalize the actual differential of a smooth potential along
an arbitrary smooth parameterization. The center differential is the original momentum,
so the constructed scale equals one there. No constant-energy premise is supplied. -/
theorem exists_constantEnergy_potentialNormalData [FiniteDimensional ℝ E]
    (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {f : E → ℝ} {σ : W → E} {Ω : Set E} {V : Set W} {w₀ : W}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hV : IsOpen V) (hw₀ : w₀ ∈ V) (hσ : ContDiffOn ℝ ∞ σ V) (hσΩ : MapsTo σ V Ω)
    {v₀ : E} (hz : (σ w₀, v₀) ∈ chartEnergyDomain x₀)
    (hmatch : fderiv ℝ f (σ w₀) = fiberLegendre (F.chartEnergy x₀) (σ w₀, v₀)) :
    ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (U : Set W) (v : W → E) (a : W → ℝ),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀) ∧
      (σ w₀, v₀) ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      IsOpen U ∧ w₀ ∈ U ∧ U ⊆ V ∧
      ContDiffOn ℝ ∞ v U ∧ ContDiffOn ℝ ∞ a U ∧ v w₀ = v₀ ∧ a w₀ = 1 ∧
      ∀ w ∈ U, (σ w, v w) ∈ e.source ∧ 0 < a w ∧
        F.chartEnergy x₀ (σ w, v w) = F.chartEnergy x₀ (σ w₀, v₀) ∧
        fiberLegendre (F.chartEnergy x₀) (σ w, v w) = a w • fderiv ℝ f (σ w) ∧
        e.symm (potentialConormalState f σ a w) = (σ w, v w) := by
  obtain ⟨e, he, hzs, _, hsub, hG, _, _, _⟩ :=
    hF.exists_smooth_chartHamiltonian x₀ hz
  have hq : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ f (σ w)) V :=
    (hf.fderiv_of_isOpen hΩ (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))).comp hσ hσΩ
  obtain ⟨U, v, a, hU, hwU, hUV, hv, ha, hv₀, ha₀, hdata⟩ :=
    hF.exists_constantEnergy_covectorData_on_branch x₀ hV hw₀ hσ hq he hzs hsub hG hmatch
  exact ⟨e, U, v, a, he, hzs, hsub, hG, hU, hwU, hUV, hv, ha, hv₀, ha₀, hdata⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
