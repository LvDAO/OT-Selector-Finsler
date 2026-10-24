import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.NormedSpace.FiberNormComparison

/-!
## Lemma skeleton

* **Conditions:** A continuous positive absolutely homogeneous finite length on the actual tangent bundle; finite-dimensionality only for uniform chart comparisons.
* **Objects:** ContinuousFinslerNorm and its ENorm/path-length adapter.
* **Proof detail:** Install absolute homogeneity, obtain trivialization bounds from compact unit spheres, and transfer them through chart derivatives.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 2, pp. 304–305 (Minkowski norms and Finsler metrics), p. 308 (Legendre duality, equation (2–12)).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006 author manuscript)*, Section 1.1, Remarks 1.3(6)–(9), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=4
* D. Bao; S.-S. Chern; Z. Shen, *An Introduction to Riemann-Finsler Geometry (Springer 2000)*, Section 1.1, pp. 2–4 (definitions); Section 6.2A–C, pp. 146–150 (local comparison and manifold/metric topology).
  https://link.springer.com/content/pdf/bfm:978-1-4612-1268-3/1#page=16

**Relationship to the sources:** The named primitive does not assume fiber convexity, subadditivity, differentiability or strong convexity. It is a weaker reversible length interface. Standard smooth Finsler structure is imposed later by IsSmoothStronglyConvex.
-/

/-!
# Continuous Finsler fiber lengths and derived coordinate bounds

The input is a finite nonnegative length on the actual tangent bundle, continuous in the bundle
topology, positive on nonzero vectors, and absolutely homogeneous. These hypotheses include
continuous reversible Finsler norms and do not require an inner product. The comparison theorems
use compactness of the reference unit sphere to derive locally uniform two-sided bounds, then
identify tangent trivializations with chart differentials. No local comparison is assumed.

The construction needs only a C¹ manifold. Convexity and additional smoothness of a Finsler norm
are not needed for these length bounds. Metric compatibility is proved in `FinslerLengthMetric`.
-/

open Set Filter Bundle Manifold
open scoped Topology NNReal ENNReal ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

/-- Continuous positive reversible homogeneous lengths on the actual tangent bundle. -/
structure ContinuousFinslerNorm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] where
  toFun : TangentBundle 𝓘(ℝ, E) M → ℝ≥0
  continuous_toFun : Continuous toFun
  map_smul : ∀ (x : M) (r : ℝ) (v : TangentSpace 𝓘(ℝ, E) x),
    toFun ⟨x, r • v⟩ = ‖r‖₊ * toFun ⟨x, v⟩
  pos : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), v ≠ 0 → 0 < toFun ⟨x, v⟩

namespace ContinuousFinslerNorm

variable (F : ContinuousFinslerNorm E M)

/-- The assigned extended norm is exactly the given finite fiber length. -/
@[instance_reducible] def enorm (x : M) : ENorm (TangentSpace 𝓘(ℝ, E) x) where
  enorm v := (F.toFun ⟨x, v⟩ : ℝ≥0∞)

/-- Absolute homogeneity supplies the class used by the path-length API. -/
theorem enormSMulClass (x : M) :
    letI := F.enorm x
    ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  let := F.enorm x
  constructor
  intro r v
  change (F.toFun ⟨x, r • v⟩ : ℝ≥0∞) = ‖r‖ₑ * (F.toFun ⟨x, v⟩ : ℝ≥0∞)
  rw [F.map_smul, ENNReal.coe_mul]
  rfl

/-- The given length vanishes at the zero tangent vector. -/
@[simp] theorem map_zero (x : M) : F.toFun ⟨x, (0 : TangentSpace 𝓘(ℝ, E) x)⟩ = 0 := by
  simpa using F.map_smul x 0 0

variable [FiniteDimensional ℝ E]

/-- The original fiber length has locally uniform two-sided bounds in a tangent trivialization. -/
theorem eventually_trivialization_bounds (x₀ : M) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ x in 𝓝 x₀, ∀ v : E,
      c * ‖v‖ ≤ (F.toFun ⟨x,
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x v⟩ : ℝ) ∧
      (F.toFun ⟨x,
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x v⟩ : ℝ) ≤ C * ‖v‖ := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀
  let G : e.baseSet → E → ℝ := fun x v ↦
    (F.toFun ⟨(x : M), (e.continuousLinearEquivAt ℝ x x.property).symm v⟩ : ℝ)
  have htot : Continuous (fun p : e.baseSet × E ↦
      (⟨(p.1 : M), e.symm (p.1 : M) p.2⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    exact e.continuousOn_symm.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p ↦ ⟨p.1.property, mem_univ _⟩)
  have hG : Continuous (Function.uncurry G) :=
    NNReal.continuous_coe.comp (F.continuous_toFun.comp htot)
  have hsmul : ∀ (x : e.baseSet) (r : ℝ) (v : E), G x (r • v) = |r| * G x v := by
    intro x r v
    dsimp only [G]
    rw [_root_.map_smul, F.map_smul, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  have hpos : ∀ (x : e.baseSet) (v : E), v ≠ 0 → 0 < G x v := by
    intro x v hv
    apply NNReal.coe_pos.mpr
    apply F.pos
    intro heq
    exact hv ((e.continuousLinearEquivAt ℝ x x.property).symm.injective
      (heq.trans ((e.continuousLinearEquivAt ℝ x x.property).symm.map_zero).symm))
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  obtain ⟨c, C, hc, hcC, hcomp⟩ := eventually_fiberNorm_comparable hG hsmul hpos ⟨x₀, hx₀⟩
  rw [nhds_subtype_eq_comap] at hcomp
  obtain ⟨U, hU, hUc⟩ := Filter.mem_comap.mp hcomp
  refine ⟨c, C, hc, hcC, ?_⟩
  filter_upwards [hU, e.open_baseSet.mem_nhds hx₀] with x hx hxbase
  intro v
  have h := hUc (show (⟨x, hxbase⟩ : e.baseSet) ∈ Subtype.val ⁻¹' U from hx) v
  simpa only [G, e.symm_continuousLinearEquivAt_eq hxbase] using h

set_option backward.isDefEq.respectTransparency false in
/-- The chart differential is bounded by the original fiber length near its center. -/
theorem eventually_chart_bound (x₀ : M) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ x in 𝓝 x₀, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v‖ₑ ≤
        C * (F.toFun ⟨x, v⟩ : ℝ≥0∞) := by
  obtain ⟨c, D, hc, _, hcomp⟩ := F.eventually_trivialization_bounds x₀
  let C : ℝ≥0 := ⟨c⁻¹, inv_nonneg.mpr hc.le⟩
  refine ⟨C, by exact_mod_cast inv_pos.mpr hc, ?_⟩
  filter_upwards [hcomp, chart_source_mem_nhds E x₀] with x hx hxs
  intro v
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀
  have hbase : x ∈ e.baseSet := hxs
  have h := (hx (e.continuousLinearMapAt ℝ x v)).1
  rw [e.symmL_continuousLinearMapAt hbase] at h
  have hreal : ‖e.continuousLinearMapAt ℝ x v‖ ≤ (C : ℝ) * (F.toFun ⟨x, v⟩ : ℝ) := by
    dsimp only [C]
    exact (le_inv_mul_iff₀ hc).mpr h
  have hnn : ‖e.continuousLinearMapAt ℝ x v‖₊ ≤ C * F.toFun ⟨x, v⟩ := by
    exact_mod_cast hreal
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℝ, E)) hxs] at hnn
  exact_mod_cast hnn

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-chart differential has a uniform bound in the original fiber length. -/
theorem eventually_inverse_chart_bound_comp (x₀ : M) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ x in 𝓝 x₀, ∀ v : E,
      (F.toFun ⟨(extChartAt 𝓘(ℝ, E) x₀).symm (extChartAt 𝓘(ℝ, E) x₀ x),
        mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm
          (range 𝓘(ℝ, E)) (extChartAt 𝓘(ℝ, E) x₀ x) v⟩ : ℝ≥0∞) ≤ C * ‖v‖ₑ := by
  obtain ⟨c, D, hc, hcD, hcomp⟩ := F.eventually_trivialization_bounds x₀
  let C : ℝ≥0 := ⟨D, hc.le.trans hcD⟩
  refine ⟨C, by exact_mod_cast hc.trans_le hcD, ?_⟩
  filter_upwards [hcomp, chart_source_mem_nhds E x₀] with x hx hxs
  intro v
  have hnn : F.toFun ⟨x,
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x v⟩ ≤ C * ‖v‖₊ := by
    exact_mod_cast (hx v).2
  have hi : (extChartAt 𝓘(ℝ, E) x₀).symm (extChartAt 𝓘(ℝ, E) x₀ x) = x :=
    (extChartAt 𝓘(ℝ, E) x₀).left_inv (by simpa using hxs)
  rw [TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, E)) hxs] at hnn
  have hcast := ENNReal.coe_le_coe.mpr hnn
  convert! hcast using 1
  congr 2
  exact TotalSpace.ext hi (heq_of_eq rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-chart estimate holds on a model neighborhood, as needed for chart segments. -/
theorem eventually_inverse_chart_bound (x₀ : M) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ y in 𝓝[range 𝓘(ℝ, E)] (extChartAt 𝓘(ℝ, E) x₀ x₀),
      ∀ v : E,
      (F.toFun ⟨(extChartAt 𝓘(ℝ, E) x₀).symm y,
        mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm
          (range 𝓘(ℝ, E)) y v⟩ : ℝ≥0∞) ≤ C * ‖v‖ₑ := by
  obtain ⟨C, hC, hbound⟩ := F.eventually_inverse_chart_bound_comp x₀
  refine ⟨C, hC, ?_⟩
  have hi : 𝓝 x₀ = 𝓝 ((extChartAt 𝓘(ℝ, E) x₀).symm
      (extChartAt 𝓘(ℝ, E) x₀ x₀)) := by simp
  rw [hi] at hbound
  have hc := continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) x₀
  filter_upwards [nhdsWithin_le_nhds (hc.preimage_mem_nhds hbound),
    extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) x₀] with y hy hyt
  have heq : y = (extChartAt 𝓘(ℝ, E) x₀) ((extChartAt 𝓘(ℝ, E) x₀).symm y) := by
    simp [-extChartAt, hyt]
  simp only [mem_preimage, mem_ofPred_eq] at hy
  convert! hy

end ContinuousFinslerNorm
end OTSelector.Geometry
