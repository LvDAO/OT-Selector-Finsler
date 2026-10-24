import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.ManifoldTubeCalibration

* **Conditions:** The same actual manifold tube, unit energy and actual Gauss momentum normality.
* **Objects:** Inverse tube time as a genuine local calibration whose differential is the original intrinsic energy momentum.
* **Proof detail:** Pair momentum with the true time and label columns, invert that differential identity and transfer the covector across actual manifold charts.

Mathematical sources:
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): The exact-one-form local calibration is derived for the actual tube without requiring one chart over its whole image.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerManifoldTubeCalibration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerManifoldTubeCalibration`; the selected original proof blocks follow. -/
section

/-!
# Calibration of the same actual Finsler manifold tube

The original energy momentum pairs with the time column as one at unit speed and
annihilates the parameter columns by Gauss normality. The actual inverse tube time
therefore gives a local calibration, without a chart containing the whole tube.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Unit original speed and actual Gauss normality identify the complete time-parameter
pairing with original energy momentum in every chart legal at the selected point. -/
theorem chartMomentum_pairing_timeLabel_of_unit (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (old : M) (t : ℝ)
    (hx : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hunit : (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) : ℝ) = 1)
    (hnormal : ∀ ξ : W, (F.chartMomentumFamily old Γ (w, t)).2
      (fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v t)) w ξ) = 0)
    (d : ℝ × W) :
    (F.chartMomentumFamily old Γ (w, t)).2
      (fderiv ℝ (fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1)) (t, w) d) =
        d.1 := by
  let γ := fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1)
  let D := fderiv ℝ γ (t, w)
  let p := (F.chartMomentumFamily old Γ (w, t)).2
  have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
    ((hB.prod isOpen_univ).mem_nhds (show (w, t) ∈ B ×ˢ univ from ⟨hw, mem_univ _⟩))
  have hs : ContMDiffAt 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) 2
      (fun q ↦ Γ q.2 q.1) (t, w) :=
    hp.comp (t, w) ((contDiffAt_snd.prodMk contDiffAt_fst).contMDiffAt)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (extChartAt 𝓘(ℝ, E) old)
      (Γ w t) := contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  have hd : HasFDerivAt γ D (t, w) :=
    ((hc.comp (t, w) hs).contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
  have htime : D (1, 0) = deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t := by
    exact (hd.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t w))).deriv.symm
  have hlabel (ξ : W) :
      D (0, ξ) = fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v t)) w ξ := by
    have hl := hd.comp w ((hasFDerivAt_const t w).prodMk (hasFDerivAt_id w))
    simpa [γ, Function.comp_def] using congrArg (fun A : W →L[ℝ] E ↦ A ξ) hl.fderiv.symm
  obtain ⟨hread, hz⟩ := hF.chartTangent_of_isEulerLagrangeAt (hEL w hw t (mem_univ _)) old hx
  have hlength : (F.chartLength old ((extChartAt 𝓘(ℝ, E) old ∘ Γ w) t,
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t) : ℝ) = 1 := by
    unfold ContinuousFinslerNorm.chartLength
    rw [← hread, (extChartAt _ _).left_inv]
    · exact hunit
    · simpa only [FiberBundle.chartedSpace_chartAt, mfld_simps] using hx
  have htimePair : p (D (1, 0)) = 1 := by
    rw [htime]
    change fiberLegendre (F.chartEnergy old) _ _ = 1
    rw [hF.chartLegendre_self_eq_chartLength_sq old hz, hlength]
    norm_num
  have hsplit : D d = d.1 • D (1, 0) + D (0, d.2) := by
    rw [← _root_.map_smul, ← map_add]
    congr 1
    simp
  change p (D d) = d.1
  rw [hsplit, map_add, _root_.map_smul, htimePair, hlabel, hnormal]
  simp

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual chart energy momentum pulls back to the original fiber-energy differential
at the same tangent vector. This identifies the covector intrinsically across charts. -/
theorem chartEnergy_fderiv_comp_mfderiv (hF : F.IsSmoothStronglyConvex) (old : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (v : TangentSpace 𝓘(ℝ, E) x)
    (hz : (extChartAt 𝓘(ℝ, E) old x,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x v) ∈
        chartEnergyDomain old) :
    (fiberLegendre (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old x,
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x v)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x) =
        fderiv ℝ (F.fiberEnergy x) v := by
  let : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := ‹NormedSpace ℝ E›
  let A : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x
  let g : E → ℝ := fun w ↦ F.chartEnergy old (extChartAt 𝓘(ℝ, E) old x, w)
  have hcoord : ContDiffAt ℝ ∞
      (fun w : E ↦ (extChartAt 𝓘(ℝ, E) old x, w)) (A v) :=
    contDiffAt_const.prodMk contDiffAt_id
  have henergy : ContDiffAt ℝ ∞ (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old x, A v) :=
    (hF.contDiffOn_chartEnergy old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds hz)
  have hd : DifferentiableAt ℝ g (A v) :=
    (henergy.comp (A v) hcoord).differentiableAt (by simp)
  have heq : g ∘ A = F.fiberEnergy x := by
    funext w
    change F.energy ((extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
      (extChartAt 𝓘(ℝ, E) old x,
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x w)) = _
    rw [ContinuousFinslerNorm.tangentChart_symm_mfderiv_extChartAt old hx]
    rfl
  have h := (hd.hasFDerivAt.comp v A.hasFDerivAt).fderiv
  rw [heq] at h
  exact h.symm

private theorem chartMomentum_comp_mfderiv_eq_fiberEnergy (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t)
    (ht : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    (fiberLegendre (F.chartEnergy old) ((extChartAt 𝓘(ℝ, E) old ∘ c) t,
      deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (c t)) =
        fderiv ℝ (F.fiberEnergy (c t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) := by
  have hchart : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (c t) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hvel : deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (c t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) := by
    have h := mfderiv_comp_apply t hchart ht (1 : ℝ)
    rw [mfderiv_eq_fderiv] at h
    exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).symm.trans h
  have hz := (hF.chartTangent_of_isEulerLagrangeAt hc old hx).2
  rw [hvel] at hz ⊢
  exact hF.chartEnergy_fderiv_comp_mfderiv old hx _ hz

/-- The actual inverse time differential is the transported chart energy momentum
composed with the genuine chart differential, in every chart legal at the selected point. -/
theorem mfderiv_manifoldTubeTime_eq_chartMomentum (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (e : OpenPartialHomeomorph (ℝ × W) M)
    (heq : (e : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    (hsource : e.source ⊆ univ ×ˢ B)
    (hinverse : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) 2 e.symm e.target)
    {t : ℝ} {w : W} (hq : (t, w) ∈ e.source) (t₀ : ℝ) (old : M)
    (hx : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hunit : (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) : ℝ) = 1)
    (hnormal : ∀ ξ : W, (F.chartMomentumFamily old Γ (w, t)).2
      (fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v t)) w ξ) = 0) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) (Γ w t) =
      (F.chartMomentumFamily old Γ (w, t)).2.comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ w t)) := by
  have hw : w ∈ B := (hsource hq).2
  have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
    ((hB.prod isOpen_univ).mem_nhds (show (w, t) ∈ B ×ˢ univ from ⟨hw, mem_univ _⟩))
  have he : MDifferentiableAt 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e (t, w) := by
    rw [heq]
    exact (hp.comp (t, w) ((contDiffAt_snd.prodMk contDiffAt_fst).contMDiffAt)).mdifferentiableAt
      (by norm_num)
  have hi := (hinverse.contMDiffAt (e.open_target.mem_nhds (e.map_source hq))).mdifferentiableAt
    (by norm_num)
  have heval : e (t, w) = Γ w t := congrFun heq (t, w)
  have hchart : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old)
      (e (t, w)) := by
    rw [heval]
    exact mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  let A := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (e (t, w))
  let p := (F.chartMomentumFamily old Γ (w, t)).2
  have hchain : fderiv ℝ
      (fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1)) (t, w) =
      A.comp (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e (t, w)) := by
    have h := mfderiv_comp (t, w) hchart he
    rw [mfderiv_eq_fderiv] at h
    change fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ (e : ℝ × W → M)) (t, w) =
      A.comp (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e (t, w)) at h
    conv_lhs at h => rw [heq]
    exact h
  have hpair (d : ℝ × W) :
      (p.comp A) (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e (t, w) d) = 1 * d.1 := by
    have h := hF.chartMomentum_pairing_timeLabel_of_unit hB hEL hG hw old t hx
      hunit hnormal d
    rw [hchain] at h
    change p (A (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e (t, w) d)) = d.1 at h
    simpa only [ContinuousLinearMap.comp_apply, one_mul] using! h
  have hd := mfderiv_manifoldFlowTimePotential_of_pairing e hq he hi (p.comp A)
    one_ne_zero hpair 1 t₀
  have hresult : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) (Γ w t) =
      p.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ w t)) := by
    simp only [one_div, inv_one, one_smul] at hd
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) (e (t, w)) =
      p.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (e (t, w))) at hd
    rw [heval] at hd
    exact hd
  exact hresult

/-- The inverse time of the same actual tube has the intrinsic original energy
momentum as its differential at unit speed. Only a chart at the selected point is used. -/
theorem mfderiv_manifoldTubeTime_eq_fiberEnergy (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (e : OpenPartialHomeomorph (ℝ × W) M)
    (heq : (e : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    (hsource : e.source ⊆ univ ×ˢ B)
    (hinverse : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) 2 e.symm e.target)
    {t : ℝ} {w : W} (hq : (t, w) ∈ e.source) (t₀ : ℝ) (old : M)
    (hx : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hunit : (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) : ℝ) = 1)
    (hnormal : ∀ ξ : W, (F.chartMomentumFamily old Γ (w, t)).2
      (fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v t)) w ξ) = 0) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) (Γ w t) =
      fderiv ℝ (F.fiberEnergy (Γ w t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) t 1) := by
  have hw : w ∈ B := (hsource hq).2
  have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
    ((hB.prod isOpen_univ).mem_nhds (show (w, t) ∈ B ×ˢ univ from ⟨hw, mem_univ _⟩))
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) t :=
    (hp.comp t ((contDiffAt_const.prodMk contDiffAt_id).contMDiffAt)).mdifferentiableAt
      (by norm_num)
  rw [hF.mfderiv_manifoldTubeTime_eq_chartMomentum hB hEL hG e heq hsource hinverse
    hq t₀ old hx hunit hnormal]
  exact hF.chartMomentum_comp_mfderiv_eq_fiberEnergy (hEL w hw t (mem_univ _)) ht old hx

/-- The same unit-speed normal family and its actual C2 tube inverse construct a C2
local time calibration. Its differential is bounded by the original Finsler length in
all tangent directions, and its derivative along every tube time curve is one. -/
theorem manifoldTubeTime_calibration (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (e : OpenPartialHomeomorph (ℝ × W) M)
    (heq : (e : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    (hsource : e.source ⊆ univ ×ˢ B)
    (hinverse : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) 2 e.symm e.target)
    (hunit : ∀ q ∈ e.source,
      (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) : ℝ) = 1)
    (hnormal : ∀ q ∈ e.source, ∀ old : M,
      Γ q.2 q.1 ∈ (extChartAt 𝓘(ℝ, E) old).source → ∀ ξ : W,
        (F.chartMomentumFamily old Γ (q.2, q.1)).2
          (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w q.1)) q.2 ξ) = 0)
    (t₀ : ℝ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (manifoldFlowTimePotential e 1 t₀) e.target ∧
      (∀ x ∈ e.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
        @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) x v)
          (F.toFun ⟨x, v⟩ : ℝ)) ∧
      ∀ q ∈ e.source,
        manifoldFlowTimePotential e 1 t₀ (Γ q.2 q.1) = q.1 - t₀ ∧
        HasDerivAt (fun t ↦ manifoldFlowTimePotential e 1 t₀ (Γ q.2 t)) 1 q.1 ∧
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) (Γ q.2 q.1) =
          fderiv ℝ (F.fiberEnergy (Γ q.2 q.1))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) q.1 1) := by
  have hbound (q : ℝ × W) (hq : q ∈ e.source)
      (v : TangentSpace 𝓘(ℝ, E) (Γ q.2 q.1)) :
      @LE.le ℝ _
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) (Γ q.2 q.1) v)
        (F.toFun ⟨Γ q.2 q.1, v⟩ : ℝ) := by
    let old := Γ q.2 q.1
    have hx : Γ q.2 q.1 ∈ (extChartAt 𝓘(ℝ, E) old).source := mem_extChartAt_source old
    have hw : q.2 ∈ B := (hsource hq).2
    obtain ⟨hread, hz⟩ :=
      hF.chartTangent_of_isEulerLagrangeAt (hEL q.2 hw q.1 (mem_univ _)) old hx
    have hlength : (F.chartLength old ((extChartAt 𝓘(ℝ, E) old ∘ Γ q.2) q.1,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ q.2) q.1) : ℝ) = 1 := by
      unfold ContinuousFinslerNorm.chartLength
      rw [← hread, (extChartAt _ _).left_inv]
      · exact hunit q hq
      · simpa only [FiberBundle.chartedSpace_chartAt, mfld_simps] using hx
    have hineq := hF.chart_fundamental_inequality old hz
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q.2 q.1) v)
    rw [hlength, one_mul] at hineq
    rw [hF.mfderiv_manifoldTubeTime_eq_chartMomentum hB hEL hG e heq hsource hinverse
      hq t₀ old hx (hunit q hq) (hnormal q hq old hx)]
    change fiberLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ q.2) q.1,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ q.2) q.1)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q.2 q.1) v) ≤ _
    simpa only [Prod.fst, Function.comp_apply,
      F.chartLength_mfderiv_extChartAt old hx] using! hineq
  refine ⟨contMDiffOn_manifoldFlowTimePotential e hinverse 1 t₀, ?_, ?_⟩
  · intro x hx
    have hq := e.map_target hx
    have heval : Γ (e.symm x).2 (e.symm x).1 = x :=
      (congrFun heq (e.symm x)).symm.trans (e.right_inv hx)
    have h := hbound (e.symm x) hq
    rw [heval] at h
    exact h
  · intro q hq
    refine ⟨?_, ?_, ?_⟩
    · simpa only [heq, one_mul] using manifoldFlowTimePotential_apply e 1 t₀ hq
    · simpa only [heq] using hasDerivAt_manifoldFlowTimePotential_curve e 1 t₀ hq
    · exact hF.mfderiv_manifoldTubeTime_eq_fiberEnergy hB hEL hG e heq hsource hinverse
        hq t₀ (Γ q.2 q.1) (mem_extChartAt_source _) (hunit q hq)
        (hnormal q hq (Γ q.2 q.1) (mem_extChartAt_source _))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
