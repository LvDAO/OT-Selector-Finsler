import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

/-!
## Lemma skeleton

* **Conditions:** Continuous positive absolutely one-homogeneous real lengths on finite-dimensional fibers, with a topological parameter.
* **Objects:** Locally uniform upper and positive lower multiples of the ambient norm.
* **Proof detail:** Take extrema on the compact unit sphere near the parameter, then rescale every nonzero vector.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006 author manuscript)*, Section 1.1, Remarks 1.3(6)–(9), pp. 4–5.
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=4
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** The sphere argument needs neither differentiability nor convexity. The parameter-uniform version is a proved generalization of the textbook fixed-Minkowski-norm bound.
-/

/-!
# Local uniform comparison for continuous fiber norms

A finite-dimensional real normed model space has a compact unit sphere. For a jointly
continuous family of real-valued, positive, absolutely homogeneous fiber lengths, compactness
gives positive lower and finite upper bounds on the sphere near each base point. Homogeneity
then gives a single two-sided comparison with the reference norm for every vector throughout
one open base neighborhood. No inner product or comparison bound is assumed.

These hypotheses hold for continuous reversible Finsler norms in a tangent trivialization.
The proofs do not need the stronger triangle inequality or strong convexity properties.
They also cover the zero-dimensional model space. This module supplies local comparison;
it does not yet construct the induced length metric or prove its topology compatibility.
-/

open Set Filter Metric
open scoped Topology

namespace OTSelector.Geometry

variable {B E : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bounds on the unit sphere extend to all vectors by absolute homogeneity. -/
theorem homogeneous_bounds_of_unit_sphere {F : E → ℝ} {c C : ℝ}
    (hsmul : ∀ (r : ℝ) (v : E), F (r • v) = |r| * F v)
    (hunit : ∀ v : E, ‖v‖ = 1 → c ≤ F v ∧ F v ≤ C) :
    ∀ v : E, c * ‖v‖ ≤ F v ∧ F v ≤ C * ‖v‖ := by
  intro v
  by_cases hv : v = 0
  · subst v
    have hzero : F 0 = 0 := by simpa using hsmul 0 0
    simp [hzero]
  · let w : E := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
    have hvw : ‖v‖ • w = v := by
      simp [w, smul_smul, norm_ne_zero_iff.mpr hv]
    have hF : F v = ‖v‖ * F w := by
      calc
        F v = F (‖v‖ • w) := congrArg F hvw.symm
        _ = ‖v‖ * F w := by rw [hsmul, abs_of_nonneg (norm_nonneg _)]
    obtain ⟨hl, hu⟩ := hunit w hw
    constructor
    · rw [hF, mul_comm c]
      exact mul_le_mul_of_nonneg_left hl (norm_nonneg _)
    · rw [hF, mul_comm C]
      exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)

variable [FiniteDimensional ℝ E]

/-- A continuous, positive, absolutely homogeneous family is uniformly comparable with the
reference norm near each base point. Both comparison constants are derived from the family. -/
theorem eventually_fiberNorm_comparable {F : B → E → ℝ}
    (hcont : Continuous (Function.uncurry F))
    (hsmul : ∀ (x : B) (r : ℝ) (v : E), F x (r • v) = |r| * F x v)
    (hpos : ∀ (x : B) (v : E), v ≠ 0 → 0 < F x v) (x₀ : B) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ᶠ x in 𝓝 x₀, ∀ v : E, c * ‖v‖ ≤ F x v ∧ F x v ≤ C * ‖v‖ := by
  have hcompact : IsCompact (sphere (0 : E) 1) := isCompact_sphere _ _
  have hbase : Continuous (F x₀) := hcont.comp (continuous_const.prodMk continuous_id)
  obtain ⟨m, hm, hmin⟩ := hcompact.exists_forall_le' hbase.continuousOn (a := 0) (by
    intro v hv
    apply hpos x₀ v
    intro hv0
    simp [hv0] at hv)
  obtain ⟨M, hmax⟩ := hcompact.bddAbove_image hbase.continuousOn
  let c : ℝ := m / 2
  let C : ℝ := max (M + 1) c
  have hc : 0 < c := by dsimp [c]; positivity
  have hlocal : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ sphere (0 : E) 1, c < F x v ∧ F x v < C := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro v hv
    have hl : c < F x₀ v := lt_of_lt_of_le (by dsimp [c]; linarith) (hmin v hv)
    have hu : F x₀ v < C := lt_of_lt_of_le
      (lt_of_le_of_lt (hmax (mem_image_of_mem _ hv)) (by linarith)) (le_max_left _ _)
    have hcv : Tendsto (Function.uncurry F) (𝓝 (x₀, v)) (𝓝 (F x₀ v)) :=
      hcont.continuousAt
    exact (hcv.eventually_const_lt hl).and (hcv.eventually_lt_const hu)
  refine ⟨c, C, hc, le_max_right _ _, ?_⟩
  filter_upwards [hlocal] with x hx
  apply homogeneous_bounds_of_unit_sphere (hsmul x)
  intro v hv
  have hb := hx v (by simpa using hv)
  exact ⟨hb.1.le, hb.2.le⟩

/-- An explicit open base neighborhood carries the uniform two-sided comparison. -/
theorem exists_open_fiberNorm_comparable {F : B → E → ℝ}
    (hcont : Continuous (Function.uncurry F))
    (hsmul : ∀ (x : B) (r : ℝ) (v : E), F x (r • v) = |r| * F x v)
    (hpos : ∀ (x : B) (v : E), v ≠ 0 → 0 < F x v) (x₀ : B) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ x ∈ U, ∀ v : E, c * ‖v‖ ≤ F x v ∧ F x v ≤ C * ‖v‖ := by
  obtain ⟨c, C, hc, hcC, hevent⟩ := eventually_fiberNorm_comparable hcont hsmul hpos x₀
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hevent
  exact ⟨U, hUopen, hxU, c, C, hc, hcC, fun x hx ↦ hUsub hx⟩

end OTSelector.Geometry
