import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import OTSelector.Analysis.Calculus.LocalSmoothExtension
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.JointC2
import OTSelector.Analysis.ODE.Flow.LocalVariational

/-!
## Lemma skeleton

* **Conditions:** A C2 finite-dimensional autonomous field, or a smooth field on an open domain.
* **Objects:** A joint-C2 local flow on a positive closed state/time box with the spatial variational equation.
* **Proof detail:** Choose a closed box inside the C2 neighborhood; for a local field first make a smooth cutoff representative and shrink trajectories back inside the original domain.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.4, Theorem 2.10, equation (2.51), proof induction and Theorem 2.11, pp. 46–48.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=57
* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 2, section “Partitions of Unity”, pp. 40–47.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10

**Relationship to the sources:** The closed-box packaging and exact domain containment are formal adapters to Teschl’s local Ck dependence. No infinite-order joint flow is claimed.
-/

/-!
# Jointly C2 local flows on open domains

Construct a single actual local flow with joint C2 dependence on initial state and
time. The finite-dimensional open-domain result uses a compactly supported smooth
extension, then restricts that same flow to the original field's domain. Initial
state derivatives and the original variational equation are retained under both
restrictions. All radii and local bounds are derived from the stated regularity;
no metric minimizing or global continuation conclusion is asserted.
-/

open Set Filter Metric Function
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A neighborhood of the initial state and time contains a positive closed flow box. -/
theorem exists_pos_closed_flow_box_subset
    {p : E} {t₀ T : ℝ} {r : ℝ≥0} {U : Set (E × ℝ)}
    (hU : U ∈ 𝓝 (p, t₀)) (hr : 0 < r) (hT : 0 < T) :
    ∃ (r' : ℝ≥0) (T' : ℝ), 0 < r' ∧ r' ≤ r ∧ 0 < T' ∧ T' ≤ T ∧
      closedBall p r' ×ˢ Icc (t₀ - T') (t₀ + T') ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ : ∃ δ : ℝ, 0 < δ ∧ closedBall (p, t₀) δ ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp hU
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let r' : ℝ≥0 := ⟨min (r : ℝ) δ, (lt_min hrR hδ).le⟩
  let T' := min T δ
  refine ⟨r', T', ?_, ?_, lt_min hT hδ, min_le_left _ _, ?_⟩
  · change (0 : ℝ) < min (r : ℝ) δ
    exact lt_min hrR hδ
  · change min (r : ℝ) δ ≤ (r : ℝ)
    exact min_le_left _ _
  · intro z hz
    apply hsub
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    constructor
    · exact (mem_closedBall.mp hz.1).trans (min_le_right _ _)
    · have ht := hz.2
      change t₀ - min T δ ≤ z.2 ∧ z.2 ≤ t₀ + min T δ at ht
      rw [Real.dist_eq, abs_le]
      have hsmall := min_le_right T δ
      constructor <;> linarith

/-- A C2 autonomous field has a single jointly C2 local flow, retaining the actual
central initial derivative and its original variational equation. -/
theorem exists_c2Flow_of_contDiff [FiniteDimensional ℝ E] {X : E → E}
    (hX : ContDiff ℝ 2 X) (p : E) (t₀ : ℝ) :
    ∃ (r : ℝ≥0) (T : ℝ), 0 < r ∧ 0 < T ∧ ∃ Φ : E × ℝ → E,
      IsLocalFlow (fun _ ↦ X) t₀ p r (t₀ - T) (t₀ + T) Φ ∧
      ContDiffOn ℝ 2 Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T), DifferentiableAt ℝ (fun x ↦ Φ (x, t)) p) ∧
      fderiv ℝ (fun x ↦ Φ (x, t₀)) p = ContinuousLinearMap.id ℝ E ∧
      ∀ (δ : E) (t : ℝ), t ∈ Icc (t₀ - T) (t₀ + T) →
        HasDerivWithinAt (fun s ↦ fderiv ℝ (fun x ↦ Φ (x, s)) p δ)
          (fderiv ℝ X (Φ (p, t)) (fderiv ℝ (fun x ↦ Φ (x, t)) p δ))
          (Icc (t₀ - T) (t₀ + T)) t := by
  obtain ⟨r, T, hr, hT, Φ, hΦ, hdiff, hinit, hvar⟩ :=
    exists_differentiableFlow_of_contDiff (hX.of_le (by norm_num)) p t₀
  have hf : ContDiffOn ℝ 2 (uncurry (fun (_ : ℝ) ↦ X)) univ :=
    (hX.comp contDiff_snd).contDiffOn
  have ht₀ : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨W, hW, hpW, hC2⟩ := exists_contDiffOn_flow_C2 hΦ hf ht₀ hrR
  obtain ⟨r', T', hr', hrle, hT', hTle, hbox⟩ :=
    exists_pos_closed_flow_box_subset (hW.mem_nhds hpW) hr hT
  have hspace : closedBall p (r' : ℝ) ⊆ closedBall p (r : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast hrle)
  have htime : Icc (t₀ - T') (t₀ + T') ⊆ Icc (t₀ - T) (t₀ + T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨r', T', hr', hT', Φ, ?_, hC2.mono hbox,
    fun t ht ↦ hdiff t (htime ht), hinit, fun δ t ht ↦ (hvar δ t (htime ht)).mono htime⟩
  exact {
    minTime_le_initial := by linarith
    initial_le_maxTime := by linarith
    apply_initial := fun x hx ↦ hΦ.apply_initial x (hspace hx)
    hasDerivWithinAt := fun x hx t ht ↦
      (hΦ.hasDerivWithinAt x (hspace hx) t (htime ht)).mono htime
    continuousOn := hΦ.continuousOn.mono (prod_mono hspace htime)
    exists_lipschitz := by
      obtain ⟨K, hK⟩ := hΦ.exists_lipschitz
      exact ⟨K, fun t ht ↦ (hK t (htime ht)).mono hspace⟩ }

/-- An open-domain smooth field has a jointly C2 actual local flow confined to that domain.
All radii, extensions and derivative bounds are constructed from the original data. -/
theorem exists_c2Flow_in_open [FiniteDimensional ℝ E]
    {U : Set E} {X : E → E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {p : E} (hp : p ∈ U) (t₀ : ℝ) :
    ∃ (r : ℝ≥0) (T : ℝ), 0 < r ∧ 0 < T ∧ ∃ Φ : E × ℝ → E,
      IsLocalFlow (fun _ ↦ X) t₀ p r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) U ∧
      ContDiffOn ℝ 2 Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T), DifferentiableAt ℝ (fun x ↦ Φ (x, t)) p) ∧
      fderiv ℝ (fun x ↦ Φ (x, t₀)) p = ContinuousLinearMap.id ℝ E ∧
      ∀ (δ : E) (t : ℝ), t ∈ Icc (t₀ - T) (t₀ + T) →
        HasDerivWithinAt (fun s ↦ fderiv ℝ (fun x ↦ Φ (x, s)) p δ)
          (fderiv ℝ X (Φ (p, t)) (fderiv ℝ (fun x ↦ Φ (x, t)) p δ))
          (Icc (t₀ - T) (t₀ + T)) t := by
  obtain ⟨V, Y, hV, hpV, hVU, hY, _, _, hYX⟩ :=
    exists_contDiff_compactlySupported_extension hU hp hX
  obtain ⟨r, T, hr, hT, Φ, hΦ, hC2, hdiff, hinit, hvar⟩ :=
    exists_c2Flow_of_contDiff (hY.of_le (by simp)) p t₀
  obtain ⟨r', T', hr', hrle, hT', hTle, hstay⟩ :=
    hΦ.exists_shrink_mapsTo hr hT hV hpV
  have hspace : closedBall p (r' : ℝ) ⊆ closedBall p (r : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast hrle)
  have htime : Icc (t₀ - T') (t₀ + T') ⊆ Icc (t₀ - T) (t₀ + T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨r', T', hr', hT', Φ, ?_, fun q hq ↦ hVU (hstay hq),
    hC2.mono (prod_mono hspace htime), fun t ht ↦ hdiff t (htime ht), hinit, ?_⟩
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

end OTSelector.Geometry.LocalFlow
