import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import OTSelector.Analysis.Calculus.DistanceLocalizationTaylor
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationPullbackLength.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationPullbackLength`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationPullbackLength

* **Conditions:** A smooth manifold map with a nonzero image of the specified reference velocity on a compact parameter set; the map itself may have folds.
* **Objects:** Actual pullback variation length, its differential and a uniform quadratic normal-perturbation bound.
* **Proof detail:** Compose the original length with the true tangent map, check slit smoothness only on the reference image, bound the pullback Hessian compactly and apply Taylor.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_taylor.html): Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): The construction requires no injectivity of the parameter map; only the actual reference image tangent must stay nonzero.
-/

/-!
# Actual length along variations of a smooth complete flow

Length is evaluated on the actual tangent map, with one fixed reference
parameter velocity and a variable perturbation. The map may have folds: only
the reference velocity must have nonzero image. Compact phase sets then give
one quadratic estimate across all manifold coordinate charts.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original Finsler length of a reference parameter velocity plus a
perturbation, pushed through the actual differential of a manifold map. -/
def mapVariationLength (F : ContinuousFinslerNorm E M) (f : V → M)
    (v₀ : V) (q : V × V) : ℝ :=
  (F.toFun (tangentMap 𝓘(ℝ, V) 𝓘(ℝ, E) f ⟨q.1, v₀ + q.2⟩) : ℝ)

/-- At every differentiability point of a parameter path, the pullback length
is exactly the original speed of its physical image. -/
theorem mapVariationLength_eq_speed (F : ContinuousFinslerNorm E M)
    {f : V → M} {z : ℝ → V} {s : ℝ} {v₀ v : V}
    (hf : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) f (z s))
    (hz : HasDerivAt z (v₀ + v) s) :
    F.mapVariationLength f v₀ (z s, v) =
      (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f ∘ z) ⟨s, (1 : ℝ)⟩) : ℝ) := by
  have hd := mfderiv_comp_apply s hf hz.differentiableAt.mdifferentiableAt (1 : ℝ)
  have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) z s (1 : ℝ) = v₀ + v := by
    rw [mfderiv_eq_fderiv]
    exact hz.deriv
  exact (congrArg (fun w ↦ (F.toFun ⟨f (z s), w⟩ : ℝ))
    (hd.trans (congrArg (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f (z s)) hv))).symm

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M}

private theorem contMDiffOn_model_tangentMap {f : V → M} {U : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U) :
    ContMDiffOn 𝓘(ℝ, V × V) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : V × V ↦ tangentMap 𝓘(ℝ, V) 𝓘(ℝ, E) f ⟨z.1, z.2⟩)
      (U ×ˢ univ) := by
  have ht := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn
  have hp : ContMDiff 𝓘(ℝ, V × V) (𝓘(ℝ, V).prod 𝓘(ℝ, V)) ∞
      (fun z : V × V ↦ (⟨z.1, z.2⟩ : TangentBundle 𝓘(ℝ, V) V)) := by
    simpa only [← modelWithCornersSelf_prod] using!
      (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, V)) (n := ∞))
  apply (ht.comp hp.contMDiffOn (fun z hz ↦ hz.1)).congr
  intro z hz
  simp only [Function.comp_def, tangentMapWithin, tangentMap,
    mfderivWithin_of_mem_nhds (hU.mem_nhds hz.1)]

/-- Smoothness of the actual pullback length requires only a nonzero image of
the reference velocity, so the manifold map need not be injective. -/
theorem contDiffAt_mapVariationLength (hF : F.IsSmoothStronglyConvex)
    {f : V → M} {U : Set V} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U) (v₀ : V)
    {q : V × V} (hq : q.1 ∈ U)
    (hne : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q.1 (v₀ + q.2) ≠ 0) :
    ContDiffAt ℝ ∞ (F.mapVariationLength f v₀) q := by
  let T := fun z : V × V ↦ tangentMap 𝓘(ℝ, V) 𝓘(ℝ, E) f ⟨z.1, v₀ + z.2⟩
  have ht := contMDiffOn_model_tangentMap hU hf
  have ha : ContDiff ℝ ∞ (fun z : V × V ↦ (z.1, v₀ + z.2)) :=
    contDiff_fst.prodMk (contDiff_const.add contDiff_snd)
  have hT : ContMDiffAt 𝓘(ℝ, V × V) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ T q :=
    (ht.contMDiffAt ((hU.prod isOpen_univ).mem_nhds
      (show (q.1, v₀ + q.2) ∈ U ×ˢ univ from ⟨hq, mem_univ _⟩))).comp q
        ha.contDiffAt.contMDiffAt
  have he : ContDiffAt ℝ ∞ (F.energy ∘ T) q :=
    ((hF.contMDiffOn_energy.contMDiffAt (F.isOpen_slitTangent.mem_nhds hne)).comp q hT).contDiffAt
  have hp : 0 < 2 * F.energy (T q) := mul_pos (by norm_num)
    (F.fiberEnergy_pos (T q).1 hne)
  have hs := (contDiffAt_const.mul he).sqrt hp.ne'
  apply hs.congr_of_eventuallyEq (Eventually.of_forall ?_)
  intro z
  change (F.toFun (T z) : ℝ) = Real.sqrt (2 * ((F.toFun (T z) : ℝ) ^ 2 / 2))
  rw [show 2 * ((F.toFun (T z) : ℝ) ^ 2 / 2) = (F.toFun (T z) : ℝ) ^ 2 by ring,
    Real.sqrt_sq (NNReal.coe_nonneg _)]

/-- Compactness in the original smooth parameter domain supplies one quadratic
upper bound for all actual normal perturbations, across arbitrary output charts. -/
theorem exists_uniform_mapVariationLength_upper [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) {f : V → M} {U K : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (v₀ : V)
    (hne : ∀ q ∈ K, mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q v₀ ≠ 0) :
    ∃ r > 0, ∃ C : ℝ≥0, ∀ q ∈ K, ∀ v : V, ‖v‖ ≤ r →
      fderiv ℝ (fun w ↦ F.mapVariationLength f v₀ (q, w)) 0 v = 0 →
      F.mapVariationLength f v₀ (q, v) ≤ F.mapVariationLength f v₀ (q, 0) +
        (C : ℝ) * ‖v‖ ^ 2 := by
  let H := F.mapVariationLength f v₀
  have hcenter (q : V) (hq : q ∈ K) : ContDiffAt ℝ ∞ H (q, 0) :=
    hF.contDiffAt_mapVariationLength hU hf v₀ (hKU hq) (by simpa using hne q hq)
  have hK' : IsCompact ((fun q : V ↦ (q, (0 : V))) '' K) :=
    hK.image (continuous_id.prodMk continuous_const)
  obtain ⟨r, hr, C, hb⟩ := exists_uniform_linear_remainder_of_contDiffAt hK'
    (fun z hz ↦ by
      obtain ⟨q, hq, rfl⟩ := hz
      exact (hcenter q hq).of_le (by simp))
  refine ⟨r, hr, C, ?_⟩
  intro q hq v hv hzero
  have hi : HasFDerivAt (fun w : V ↦ (q, w))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) 0 :=
    (hasFDerivAt_const q 0).prodMk (hasFDerivAt_id 0)
  have hp := congrArg (fun A : V →L[ℝ] ℝ ↦ A v)
    (((hcenter q hq).differentiableAt (by simp)).hasFDerivAt.comp 0 hi).fderiv
  have hz : fderiv ℝ H (q, 0) (0, v) = 0 := hp.symm.trans hzero
  have hrem := hb (q, 0) (mem_image_of_mem _ hq) (0, v) (by simpa using hv)
  simp only [Prod.mk_add_mk, add_zero, zero_add, hz, sub_zero, Prod.norm_def,
    norm_zero, max_eq_right (norm_nonneg _)] at hrem
  have ht := (abs_le.mp hrem).2
  linarith

/-- The original length is smooth at every nonzero tangent vector in its
actual fiber; this follows from the half-square energy and positivity. -/
theorem contDiffAt_actual_fiberLength (hF : F.IsSmoothStronglyConvex)
    (x : M) {v : E} (hv : v ≠ 0) :
    ContDiffAt ℝ ∞ (fun w : E ↦ (F.toFun ⟨x, w⟩ : ℝ)) v := by
  have he : ContDiffAt ℝ ∞ (fun w : E ↦ F.energy ⟨x, w⟩) v :=
    hF.contDiffAt_fiberEnergyModel x hv
  have hp : 0 < 2 * F.energy ⟨x, v⟩ := mul_pos (by norm_num) (F.fiberEnergy_pos x hv)
  apply ((contDiffAt_const.mul he).sqrt hp.ne').congr_of_eventuallyEq
    (Eventually.of_forall ?_)
  intro w
  change (F.toFun ⟨x, w⟩ : ℝ) = Real.sqrt (2 * ((F.toFun ⟨x, w⟩ : ℝ) ^ 2 / 2))
  rw [show 2 * ((F.toFun ⟨x, w⟩ : ℝ) ^ 2 / 2) = (F.toFun ⟨x, w⟩ : ℝ) ^ 2 by ring,
    Real.sqrt_sq (NNReal.coe_nonneg _)]

/-- The derivative in the perturbation variable is the actual length momentum
composed with the same manifold differential, including when that map has folds. -/
theorem hasFDerivAt_mapVariationLength (hF : F.IsSmoothStronglyConvex)
    (f : V → M) (q v₀ : V)
    (hne : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q v₀ ≠ 0) :
    HasFDerivAt (fun w ↦ F.mapVariationLength f v₀ (q, w))
      ((fderiv ℝ (fun w : TangentSpace 𝓘(ℝ, E) (f q) ↦ (F.toFun ⟨f q, w⟩ : ℝ))
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q v₀)).comp
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q)) 0 := by
  let A : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q
  have ha : HasFDerivAt (fun w : V ↦ A (v₀ + w)) A 0 := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
      A.hasFDerivAt.comp 0 ((hasFDerivAt_id 0).const_add v₀)
  have hd : HasFDerivAt (fun w : E ↦ (F.toFun ⟨f q, w⟩ : ℝ))
      (fderiv ℝ (fun w : E ↦ (F.toFun ⟨f q, w⟩ : ℝ)) (A v₀)) (A (v₀ + 0)) := by
    simpa only [add_zero] using
      ((hF.contDiffAt_actual_fiberLength (f q) (v := A v₀) hne).differentiableAt
        (by simp)).hasFDerivAt
  simpa only [add_zero] using! hd.comp 0 ha

/-- The uniform actual length estimate can be consumed with the original
momentum orthogonality supplied by complete-flow first variation. -/
theorem exists_uniform_mapVariationLength_upper_of_momentum [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) {f : V → M} {U K : Set V}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (v₀ : V)
    (hne : ∀ q ∈ K, mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q v₀ ≠ 0) :
    ∃ r > 0, ∃ C : ℝ≥0, ∀ q ∈ K, ∀ v : V, ‖v‖ ≤ r →
      (fderiv ℝ (fun w : TangentSpace 𝓘(ℝ, E) (f q) ↦ (F.toFun ⟨f q, w⟩ : ℝ))
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q v₀))
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q v) = 0 →
      F.mapVariationLength f v₀ (q, v) ≤ F.mapVariationLength f v₀ (q, 0) +
        (C : ℝ) * ‖v‖ ^ 2 := by
  obtain ⟨r, hr, C, hb⟩ := hF.exists_uniform_mapVariationLength_upper hU hf hK hKU v₀ hne
  refine ⟨r, hr, C, fun q hq v hv hp ↦ hb q hq v hv ?_⟩
  rw [(hF.hasFDerivAt_mapVariationLength f q v₀ (hne q hq)).fderiv]
  exact hp

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
