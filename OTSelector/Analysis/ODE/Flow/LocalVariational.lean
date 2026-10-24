import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import OTSelector.Analysis.Calculus.LocalSmoothExtension
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.FrechetDerivative
import OTSelector.Analysis.ODE.Flow.Variational
import OTSelector.Analysis.ODE.Flow.VariationalSolutionOperator

/-!
## Lemma skeleton

* **Conditions:** A C1 autonomous field on a complete normed space; finite-dimensionality for localization from an open smooth field.
* **Objects:** A local flow whose initial-state derivative satisfies the variational equation.
* **Proof detail:** Shrink a local flow into a prescribed open set, construct its spatial derivative by the remainder argument, and localize a field using a smooth cutoff if needed.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.4, equations (2.46)–(2.50) and Theorem 2.10, pp. 45–47.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 2, section “Partitions of Unity”, pp. 40–47.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10

**Relationship to the sources:** This packages differentiable dependence and the variational initial identity. Open-domain localization is a finite-dimensional cutoff corollary.
-/

/-!
# Local initial-state derivatives for a smooth vector field

For a globally C1 autonomous field on a real Banach space, construct a local solution
family and prove that its actual derivative at the central initial point satisfies the
actual linearized ODE. The positive time interval and derivative bounds are obtained
from continuity along the compact reference orbit and shrinking the interval.

For a smooth field on an open subset of a finite-dimensional real normed space, use a
smooth representative of its germ and shrink the entire initial-ball/time-interval
product into the region of exact agreement. Both the original ODE and its derivative
then involve the original field. The final theorem has no global extension, chosen flow,
or derivative-bound hypothesis. It asserts initial differentiability at the specified
central point and within-interval time derivatives, not joint smooth flow dependence.
-/

open Set Filter Metric Function
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace LocalFlow

omit [CompleteSpace E] in
/-- A local flow can be restricted to a smaller initial ball and time interval inside `V`. -/
theorem IsLocalFlow.exists_shrink_mapsTo
    {f : ℝ → E → E} {t₀ T : ℝ} {p : E} {r : ℝ≥0} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hr : 0 < r) (hT : 0 < T) {V : Set E} (hV : IsOpen V) (hp : p ∈ V) :
    ∃ (r' : ℝ≥0) (T' : ℝ), 0 < r' ∧ r' ≤ r ∧ 0 < T' ∧ T' ≤ T ∧
      MapsTo Φ (closedBall p r' ×ˢ Icc (t₀ - T') (t₀ + T')) V := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcont : ContinuousAt Φ (p, t₀) :=
    hΦ.continuousOn.continuousAt
      (prod_mem_nhds (closedBall_mem_nhds p hrR)
        (Icc_mem_nhds (by linarith) (by linarith)))
  have hpΦ : Φ (p, t₀) ∈ V := by
    rw [hΦ.apply_initial p (mem_closedBall_self hrR.le)]
    exact hp
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds (hV.mem_nhds hpΦ))
  let r' : ℝ≥0 := ⟨min (r : ℝ) (δ / 2), (lt_min hrR (half_pos hδ)).le⟩
  let T' : ℝ := min T (δ / 2)
  refine ⟨r', T', ?_, ?_, lt_min hT (half_pos hδ), min_le_left _ _, ?_⟩
  · change (0 : ℝ) < min (r : ℝ) (δ / 2)
    exact lt_min hrR (half_pos hδ)
  · change min (r : ℝ) (δ / 2) ≤ (r : ℝ)
    exact min_le_left _ _
  · intro z hz
    apply hδsub
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · have hx : dist z.1 p ≤ min (r : ℝ) (δ / 2) := mem_closedBall.mp hz.1
      exact lt_of_le_of_lt (hx.trans (min_le_right _ _)) (half_lt_self hδ)
    · have ht := hz.2
      change t₀ - min T (δ / 2) ≤ z.2 ∧ z.2 ≤ t₀ + min T (δ / 2) at ht
      have hsmall := min_le_right T (δ / 2)
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith


/-- A globally C1 autonomous field has a local flow whose actual initial derivative
solves the variational ODE. The time and derivative bounds are constructed, not assumed. -/
theorem exists_differentiableFlow_of_contDiff {X : E → E}
    (hX : ContDiff ℝ 1 X) (p : E) (t₀ : ℝ) :
    ∃ (r : ℝ≥0) (T : ℝ), 0 < r ∧ 0 < T ∧ ∃ Φ : E × ℝ → E,
      IsLocalFlow (fun _ ↦ X) t₀ p r (t₀ - T) (t₀ + T) Φ ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T), DifferentiableAt ℝ (fun x ↦ Φ (x, t)) p) ∧
      fderiv ℝ (fun x ↦ Φ (x, t₀)) p = ContinuousLinearMap.id ℝ E ∧
      ∀ (δ : E) (t : ℝ), t ∈ Icc (t₀ - T) (t₀ + T) →
        HasDerivWithinAt (fun s ↦ fderiv ℝ (fun x ↦ Φ (x, s)) p δ)
          (fderiv ℝ X (Φ (p, t)) (fderiv ℝ (fun x ↦ Φ (x, t)) p δ))
          (Icc (t₀ - T) (t₀ + T)) t := by
  have hf : ContDiffOn ℝ 1 (uncurry (fun (_ : ℝ) ↦ X)) univ :=
    (hX.comp contDiff_snd).contDiffOn
  obtain ⟨r, ε, hr, hε, Φ, hΦ⟩ := exists_isLocalFlow_of_contDiffOn_univ _ hf t₀ p
  have hp : p ∈ closedBall p r := mem_closedBall_self r.coe_nonneg
  obtain ⟨M, hM, hbd⟩ := hΦ.exists_norm_fderiv_le_along_orbit hf p hp
  let T := min ε (1 / (2 * (M + 1)))
  have hden : 0 < 2 * (M + 1) := by positivity
  have hT : 0 < T := lt_min hε (div_pos zero_lt_one hden)
  have hTle : T ≤ ε := min_le_left _ _
  have hMT : M * T < 1 := by
    have ht := (le_div_iff₀ hden).mp (show T ≤ 1 / (2 * (M + 1)) from min_le_right _ _)
    nlinarith
  have hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - ε) (t₀ + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hA := (hΦ.continuousOn_fderiv_along_orbit hf p hp).mono hsub
  have hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ X (Φ (p, t))‖ ≤ M :=
    fun t ht ↦ hbd t (hsub ht)
  have hd (t : ℝ) (ht : t ∈ Icc (t₀ - T) (t₀ + T)) := hasFDerivAt_flow_at_initial_of_isLocalFlow hΦ hf
    hT hM hMT hsub hA_bd hr ht
  have hJ (t : ℝ) (ht : t ∈ Icc (t₀ - T) (t₀ + T)) (δ : E) :
      fderiv ℝ (fun x ↦ Φ (x, t)) p δ =
        variationalSolutionFun hT hM hMT hA hA_bd δ t := by
    rw [(hd t ht).fderiv]
    exact variationalLinearMapAt_apply hT hM hMT hA hA_bd ht δ
  have ht₀ : t₀ ∈ Icc (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  refine ⟨r, T, hr, hT, Φ, ?_, fun t ht ↦ (hd t ht).differentiableAt, ?_, ?_⟩
  · exact {
      minTime_le_initial := ht₀.1
      initial_le_maxTime := ht₀.2
      apply_initial := hΦ.apply_initial
      hasDerivWithinAt := fun x hx t ht ↦ (hΦ.hasDerivWithinAt x hx t (hsub ht)).mono hsub
      continuousOn := hΦ.continuousOn.mono (prod_mono Subset.rfl hsub)
      exists_lipschitz := by
        obtain ⟨K, hK⟩ := hΦ.exists_lipschitz
        exact ⟨K, fun t ht ↦ hK t (hsub ht)⟩ }
  · apply ContinuousLinearMap.ext
    intro δ
    rw [hJ t₀ ht₀ δ]
    exact (variationalSolutionFun_isSolution hT hM hMT hA hA_bd δ).1
  · intro δ t ht
    have hvar := (variationalSolutionFun_isSolution hT hM hMT hA hA_bd δ).2 t ht
    rw [hJ t ht δ]
    exact hvar.congr_of_mem (fun s hs ↦ hJ s hs δ) ht

omit [CompleteSpace E] in
/-- A smooth vector field on an open subset of a finite-dimensional real normed space
has a local family whose actual initial derivative satisfies its actual variational ODE.
The whole initial-ball/time-interval product stays in the original open set. -/
theorem exists_differentiableFlow_in_open [FiniteDimensional ℝ E]
    {U : Set E} {X : E → E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {p : E} (hp : p ∈ U) (t₀ : ℝ) :
    ∃ (r : ℝ≥0) (T : ℝ), 0 < r ∧ 0 < T ∧ ∃ Φ : E × ℝ → E,
      IsLocalFlow (fun _ ↦ X) t₀ p r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) U ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T), DifferentiableAt ℝ (fun x ↦ Φ (x, t)) p) ∧
      fderiv ℝ (fun x ↦ Φ (x, t₀)) p = ContinuousLinearMap.id ℝ E ∧
      ∀ (δ : E) (t : ℝ), t ∈ Icc (t₀ - T) (t₀ + T) →
        HasDerivWithinAt (fun s ↦ fderiv ℝ (fun x ↦ Φ (x, s)) p δ)
          (fderiv ℝ X (Φ (p, t)) (fderiv ℝ (fun x ↦ Φ (x, t)) p δ))
          (Icc (t₀ - T) (t₀ + T)) t := by
  obtain ⟨V, Y, hV, hpV, hVU, hY, _, _, hYX⟩ :=
    exists_contDiff_compactlySupported_extension hU hp hX
  obtain ⟨r, T, hr, hT, Φ, hΦ, hdiff, hinit, hvar⟩ :=
    exists_differentiableFlow_of_contDiff (hY.of_le (by simp)) p t₀
  obtain ⟨r', T', hr', hrle, hT', hTle, hstay⟩ :=
    hΦ.exists_shrink_mapsTo hr hT hV hpV
  have hspace : closedBall p (r' : ℝ) ⊆ closedBall p (r : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast hrle)
  have htime : Icc (t₀ - T') (t₀ + T') ⊆ Icc (t₀ - T) (t₀ + T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨r', T', hr', hT', Φ, ?_, fun q hq ↦ hVU (hstay hq),
    fun t ht ↦ hdiff t (htime ht), hinit, ?_⟩
  · exact {
      minTime_le_initial := by linarith
      initial_le_maxTime := by linarith
      apply_initial := fun x hx ↦ hΦ.apply_initial x (hspace hx)
      hasDerivWithinAt := fun x hx t ht ↦ by
        rw [← hYX (hstay ⟨hx, ht⟩)]
        exact (hΦ.hasDerivWithinAt x (hspace hx) t (htime ht)).mono htime
      continuousOn := hΦ.continuousOn.mono (prod_mono hspace htime)
      exists_lipschitz := by
        obtain ⟨K, hK⟩ := hΦ.exists_lipschitz
        exact ⟨K, fun t ht ↦ (hK t (htime ht)).mono hspace⟩ }
  · intro δ t ht
    have horbit : Φ (p, t) ∈ V := hstay ⟨mem_closedBall_self r'.coe_nonneg, ht⟩
    have heq : Y =ᶠ[𝓝 (Φ (p, t))] X :=
      hYX.eventuallyEq_of_mem (hV.mem_nhds horbit)
    simpa only [heq.fderiv_eq] using (hvar δ t (htime ht)).mono htime

end LocalFlow
end OTSelector.Geometry
