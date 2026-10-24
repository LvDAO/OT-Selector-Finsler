import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.ODE.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import OTSelector.Analysis.Calculus.Variational.CalibratedEnergyIdentities
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential

/-!
# Geometry.Finsler.TubeCoordinateEnergy

* **Conditions:** A genuine smooth manifold tube with smooth inverse and the actual unit/Gauss calibration identities.
* **Objects:** Original pulled-back tube energy/length, slit smoothness, positive vertical Hessian and zero actual base/mixed Hessian columns at the time velocity.
* **Proof detail:** Use the true tangent map and inverse derivative identities, pull back original fiber Hessians and differentiate actual calibration at the constant time column.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (derived): This is a coordinate expression of the original energy/cost, not a replacement Finsler structure.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateEnergy`; the selected original proof blocks follow. -/
section

/-!
# The original energy in genuine smooth tube coordinates

The energy and length are pulled back by the actual tangent map of the constructed
manifold tube. Smooth inverse identities preserve nonzero velocities. The same
original energy is therefore jointly smooth on the slit coordinate domain.
Inverse time calibration identifies its genuine constant time velocity and covector;
actual differentiation then gives zero base and mixed energy Hessian blocks.
The actual vertical Hessian transforms by the invertible tangent change and stays
strictly positive. The Euler--Lagrange and endpoint-kernel transfer to these new
coordinates remain separate steps toward actual endpoint nonconjugacy.
No tube map is identified with an original chart or used to replace the cost.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E V W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem fderiv2_comp_equiv_models {L : E → ℝ} (A : V ≃L[ℝ] E) {v : V}
    (h2 : DifferentiableAt ℝ (fderiv ℝ L) (A v)) (u w : V) :
    fderiv ℝ (fderiv ℝ (L ∘ A)) v u w =
      fderiv ℝ (fderiv ℝ L) (A v) (A u) (A w) := by
  have hfirst : fderiv ℝ (L ∘ A) = fun x ↦ (fderiv ℝ L (A x)).comp
      (A : V →L[ℝ] E) := by
    funext x
    exact A.comp_right_fderiv
  rw [hfirst]
  have hsecond := (h2.hasFDerivAt.comp v A.hasFDerivAt).clm_comp
    (hasFDerivAt_const (A : V →L[ℝ] E) v)
  have hs := hsecond.fderiv
  simp only [Function.comp_def] at hs
  rw [hs]
  simp

/-- Original energy evaluated on the actual tangent map of a genuine coordinate tube. -/
def tubeCoordinateEnergy (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (z : V × V) : ℝ :=
  F.energy (tangentMap 𝓘(ℝ, V) 𝓘(ℝ, E) Y ⟨z.1, z.2⟩)

/-- Original Finsler length evaluated on the same actual tangent coordinate change. -/
def tubeCoordinateLength (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (z : V × V) : ℝ :=
  (F.toFun (tangentMap 𝓘(ℝ, V) 𝓘(ℝ, E) Y ⟨z.1, z.2⟩) : ℝ)

/-- The original half-square energy identity is unchanged by the true tangent pullback. -/
theorem tubeCoordinateEnergy_eq_half_sq (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (z : V × V) :
    F.tubeCoordinateEnergy Y z = F.tubeCoordinateLength Y z ^ 2 / 2 := rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The actual derivative of a smooth tube is bijective, using its actual smooth inverse. -/
theorem mfderiv_tubeCoordinate_bijective {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hYi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {q : V} (hq : q ∈ Y.source) :
    Function.Bijective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q) := by
  have hd : Y.MDifferentiable 𝓘(ℝ, V) 𝓘(ℝ, E) :=
    ⟨hY.mdifferentiableOn (by simp), hYi.mdifferentiableOn (by simp)⟩
  exact hd.mfderiv_bijective hq

private theorem contMDiffOn_tube_tangent (Y : OpenPartialHomeomorph V M)
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source) :
    ContMDiffOn 𝓘(ℝ, V × V) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : V × V ↦ tangentMap 𝓘(ℝ, V) 𝓘(ℝ, E) Y ⟨z.1, z.2⟩)
      (Y.source ×ˢ univ) := by
  have ht := hY.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    Y.open_source.uniqueMDiffOn
  have hp : ContMDiff 𝓘(ℝ, V × V) (𝓘(ℝ, V).prod 𝓘(ℝ, V)) ∞
      (fun z : V × V ↦ (⟨z.1, z.2⟩ : TangentBundle 𝓘(ℝ, V) V)) := by
    simpa only [← modelWithCornersSelf_prod] using!
      (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, V)) (n := ∞))
  apply (ht.comp hp.contMDiffOn (fun z hz ↦ hz.1)).congr
  intro z hz
  simp only [Function.comp_def, tangentMapWithin, tangentMap,
    mfderivWithin_of_mem_nhds (Y.open_source.mem_nhds hz.1)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The actual time column of the same tube is the original curve's actual velocity. -/
theorem tangentMap_tubeCoordinate_timeColumn {Y : OpenPartialHomeomorph (ℝ × W) M}
    {Γ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (heq : (Y : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    {q : ℝ × W} (hq : q ∈ Y.source) :
    tangentMap 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y ⟨q, (1, 0)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩ := by
  let σ : ℝ → ℝ × W := fun t ↦ (t, q.2)
  have hσ : HasFDerivAt σ (ContinuousLinearMap.inl ℝ ℝ W) q.1 := by
    exact hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2
  have hσT : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × W) σ ⟨q.1, (1 : ℝ)⟩ =
      (⟨q, (1, 0)⟩ : TangentBundle 𝓘(ℝ, ℝ × W) (ℝ × W)) := by
    change (⟨σ q.1, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × W) σ q.1 1⟩ :
      TangentBundle 𝓘(ℝ, ℝ × W) (ℝ × W)) = _
    rw [mfderiv_eq_fderiv, hσ.fderiv]
    rfl
  have hcomp : (Y : ℝ × W → M) ∘ σ = Γ q.2 := by
    rw [heq]
    rfl
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y (σ q.1) :=
    (hY.contMDiffAt (Y.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have h := tangentMap_comp_at (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ × W))
    (I'' := 𝓘(ℝ, E)) ⟨q.1, (1 : ℝ)⟩ hd hσ.hasMFDerivAt.mdifferentiableAt
  rw [hcomp, hσT] at h
  exact h.symm

/-- Half-unit original energy of the given family supplies the actual unit time column
of the same tube; no Euler--Lagrange equation or inverse regularity is needed. -/
theorem tubeCoordinate_timeColumn_unit (F : ContinuousFinslerNorm E M)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Γ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (heq : (Y : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    {q : ℝ × W} (hq : q ∈ Y.source) :
    F.tubeCoordinateEnergy Y (q, (1, 0)) = 1 / 2 ∧
      F.tubeCoordinateLength Y (q, (1, 0)) = 1 := by
  have ht := tangentMap_tubeCoordinate_timeColumn hY heq hq
  have he : F.tubeCoordinateEnergy Y (q, (1, 0)) = 1 / 2 := by
    unfold tubeCoordinateEnergy
    rw [ht]
    exact hhalf q hq
  refine ⟨he, ?_⟩
  change (F.toFun (tangentMap 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y ⟨q, (1, 0)⟩) : ℝ) = 1
  change (F.toFun (tangentMap 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y ⟨q, (1, 0)⟩) : ℝ) ^ 2 / 2 =
    1 / 2 at he
  nlinarith [NNReal.coe_nonneg
    (F.toFun (tangentMap 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y ⟨q, (1, 0)⟩))]

/-- The original all-direction bound for the actual inverse-time potential becomes
exactly the time covector bound for original length in the genuine tube coordinates. -/
theorem tubeCoordinateLength_time_lower_bound (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph (ℝ × W) M)
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target) (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ)) {q : ℝ × W} (hq : q ∈ Y.source) (v : ℝ × W) :
    v.1 ≤ F.tubeCoordinateLength Y (q, v) := by
  have hf := (hY.contMDiffAt (Y.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have hp := ((contMDiffOn_manifoldFlowTimePotential Y hi 1 t₀).contMDiffAt
    (Y.open_target.mem_nhds (Y.map_source hq))).mdifferentiableAt (by simp)
  have heq : (manifoldFlowTimePotential Y 1 t₀ ∘ Y) =ᶠ[𝓝 q]
      (fun z : ℝ × W ↦ z.1 - t₀) := by
    filter_upwards [Y.open_source.mem_nhds hq] with z hz
    simpa only [one_mul, Function.comp_def] using manifoldFlowTimePotential_apply Y 1 t₀ hz
  have hc : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) (Y q)).comp
      (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y q) = ContinuousLinearMap.fst ℝ ℝ W := by
    rw [← mfderiv_comp q hp hf, heq.mfderiv_eq, mfderiv_eq_fderiv]
    exact (hasFDerivAt_fst.sub_const t₀).fderiv
  have hb := hbound (Y q) (Y.map_source hq) (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y q v)
  change @LE.le ℝ _ (((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
    (manifoldFlowTimePotential Y 1 t₀) (Y q)).comp
    (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y q)) v) (F.tubeCoordinateLength Y (q, v)) at hb
  rw [hc] at hb
  exact hb

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- Smoothness of the original energy in actual tube coordinates follows from the
actual smooth tube and inverse, without an assumed regular pullback Lagrangian. -/
theorem contDiffOn_tubeCoordinateEnergy (hF : F.IsSmoothStronglyConvex)
    (Y : OpenPartialHomeomorph V M)
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target) :
    ContDiffOn ℝ ∞ (F.tubeCoordinateEnergy Y) (Y.source ×ˢ {v : V | v ≠ 0}) := by
  have ht := contMDiffOn_tube_tangent Y hY
  intro z hz
  have hs : IsOpen (Y.source ×ˢ (univ : Set V)) := Y.open_source.prod isOpen_univ
  have hp := ht.contMDiffAt (hs.mem_nhds ⟨hz.1, mem_univ _⟩)
  have hinj := (mfderiv_tubeCoordinate_bijective hY hi hz.1).injective
  have hne : (tangentMap 𝓘(ℝ, V) 𝓘(ℝ, E) Y ⟨z.1, z.2⟩).2 ≠ 0 := by
    intro h
    exact hz.2 (hinj (h.trans (_root_.map_zero _).symm))
  have he := hF.contMDiffOn_energy.contMDiffAt (F.isOpen_slitTangent.mem_nhds hne)
  exact (he.comp z hp).contDiffAt.contDiffWithinAt

/-- The same actual tube pullback of length is smooth away from zero velocity. -/
theorem contDiffOn_tubeCoordinateLength (hF : F.IsSmoothStronglyConvex)
    (Y : OpenPartialHomeomorph V M)
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target) :
    ContDiffOn ℝ ∞ (F.tubeCoordinateLength Y) (Y.source ×ˢ {v : V | v ≠ 0}) := by
  have heq : F.tubeCoordinateLength Y = fun z ↦ Real.sqrt (2 * F.tubeCoordinateEnergy Y z) := by
    funext z
    rw [F.tubeCoordinateEnergy_eq_half_sq]
    rw [show 2 * (F.tubeCoordinateLength Y z ^ 2 / 2) =
      F.tubeCoordinateLength Y z ^ 2 by ring, Real.sqrt_sq]
    exact (F.toFun _).coe_nonneg
  rw [heq]
  apply (contDiffOn_const.mul (hF.contDiffOn_tubeCoordinateEnergy Y hY hi)).sqrt
  intro z hz
  have hinj := (mfderiv_tubeCoordinate_bijective hY hi hz.1).injective
  have hn : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y z.1 z.2 ≠ 0 := by
    intro h
    exact hz.2 (hinj (h.trans (_root_.map_zero _).symm))
  have hp := F.fiberEnergy_pos (Y z.1) hn
  change 2 * F.fiberEnergy (Y z.1) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y z.1 z.2) ≠ 0
  positivity

/-- The tube fiber Hessian is the original fiber-model Hessian under its actual linear
fiber change. Source and manifold model spaces may be different normed spaces. -/
theorem tubeCoordinateEnergy_fiber_hessian (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hYi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {q v : V} (hq : q ∈ Y.source) (hv : v ≠ 0) (u w : V) :
    let A := (tangentFiberModelEquiv (Y q)).symm.toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q)
    fderiv ℝ (fderiv ℝ (fun η ↦ F.tubeCoordinateEnergy Y (q, η))) v u w =
      fderiv ℝ (fderiv ℝ (F.fiberEnergyModel (Y q))) (A v) (A u) (A w) := by
  have hd : Y.MDifferentiable 𝓘(ℝ, V) 𝓘(ℝ, E) :=
    ⟨hY.mdifferentiableOn (by simp), hYi.mdifferentiableOn (by simp)⟩
  let A : V ≃L[ℝ] E := (hd.mfderiv hq).trans (tangentFiberModelEquiv (Y q)).symm
  have heq : (fun η ↦ F.tubeCoordinateEnergy Y (q, η)) = F.fiberEnergyModel (Y q) ∘ A := by
    funext η
    change F.energy ⟨Y q, mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q η⟩ =
      F.energy ⟨Y q, tangentFiberModelEquiv (Y q) (A η)⟩
    rfl
  have hAv : A v ≠ 0 := A.map_eq_zero_iff.not.mpr hv
  rw [heq, fderiv2_comp_equiv_models A (hF.differentiableAt_legendre (Y q) hAv)]
  rfl

/-- The original strong convexity remains strict in every genuine smooth tube fiber.
Injectivity of its tangent map is derived from the smooth inverse. -/
theorem tubeCoordinateEnergy_fiber_hessian_pos (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hYi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {q v w : V} (hq : q ∈ Y.source) (hv : v ≠ 0) (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (fun η ↦ F.tubeCoordinateEnergy Y (q, η))) v w w := by
  let A : V →L[ℝ] E := (tangentFiberModelEquiv (Y q)).symm.toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q)
  have hA : Function.Injective A :=
    (tangentFiberModelEquiv (Y q)).symm.injective.comp
      (mfderiv_tubeCoordinate_bijective hY hYi hq).injective
  have hAv : A v ≠ 0 := fun h ↦ hv (hA (h.trans (A.map_zero).symm))
  have hAw : A w ≠ 0 := fun h ↦ hw (hA (h.trans (A.map_zero).symm))
  rw [hF.tubeCoordinateEnergy_fiber_hessian hY hYi hq hv w w]
  exact hF.hessian_pos (Y q) (A v) hAv (A w) hAw

/-- The constructed inverse-time calibration yields the actual constant time
momentum and zero base and mixed Hessian blocks of original energy in the true tube.
Unit time speed is derived from half energy of the same actual family. -/
theorem tubeCoordinateEnergy_calibrated_identities (hF : F.IsSmoothStronglyConvex)
    (Y : OpenPartialHomeomorph (ℝ × W) M) {Γ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target) (t₀ : ℝ)
    (heq : (Y : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ)) {q : ℝ × W} (hq : q ∈ Y.source) :
    let v₀ : ℝ × W := (1, 0)
    let p := ContinuousLinearMap.fst ℝ ℝ W
    fderiv ℝ (fun w ↦ F.tubeCoordinateLength Y (q, w)) v₀ = p ∧
    F.tubeCoordinateEnergy Y (q, v₀) = 1 / 2 ∧
    fiberLegendre (F.tubeCoordinateEnergy Y) (q, v₀) = p ∧
    fderiv ℝ (fun y ↦ F.tubeCoordinateEnergy Y (y, v₀)) q = 0 ∧
    fderiv ℝ (fun y ↦ fiberLegendre (F.tubeCoordinateEnergy Y) (y, v₀)) q = 0 ∧
    fderiv ℝ (F.tubeCoordinateEnergy Y) (q, v₀) =
      p.comp (ContinuousLinearMap.snd ℝ (ℝ × W) (ℝ × W)) ∧
    (∀ u : ℝ × W, fderiv ℝ (fderiv ℝ (F.tubeCoordinateEnergy Y)) (q, v₀) (u, 0) = 0) ∧
    ∀ u : ℝ × W, ∀ z : (ℝ × W) × (ℝ × W),
      fderiv ℝ (fderiv ℝ (F.tubeCoordinateEnergy Y)) (q, v₀) z (u, 0) = 0 := by
  apply calibrated_half_sq_energy_identities (L := F.tubeCoordinateEnergy Y)
    (G := F.tubeCoordinateLength Y) Y.open_source (ContinuousLinearMap.fst ℝ ℝ W)
    (by rfl) (fun y _ w ↦ F.tubeCoordinateEnergy_eq_half_sq Y (y, w))
    (fun y hy ↦ (F.tubeCoordinate_timeColumn_unit hY heq hhalf hy).2)
    (fun y hy w ↦ F.tubeCoordinateLength_time_lower_bound Y hY hi t₀ hbound hy w)
  · intro y hy
    have hz : (y, (1, (0 : W))) ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} := ⟨hy, by simp⟩
    have hc := (hF.contDiffOn_tubeCoordinateLength Y hY hi).contDiffAt
      ((Y.open_source.prod isOpen_ne).mem_nhds hz)
    exact (hc.comp (1, (0 : W)) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      (by simp)
  · intro y hy
    have hz : (y, (1, (0 : W))) ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} := ⟨hy, by simp⟩
    exact ((hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
      ((Y.open_source.prod isOpen_ne).mem_nhds hz)).of_le (by simp)
  · exact hq

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
