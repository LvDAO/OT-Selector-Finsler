import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Geometry.Finsler.Basic

/-!
## Lemma skeleton

* **Conditions:** A C1 potential with differential bounded by a continuous positive homogeneous length, plus a C1 competitor curve; equality on the calibrated curve for minimization.
* **Objects:** Endpoint potential difference, path integral and calibrated minimizing paths.
* **Proof detail:** Integrate du(c′)≤F(c′); equality gives length=endpoint potential difference and comparison with every competitor.

## Mathematical sources

* J. C. Álvarez Paiva; A. C. Thompson, *Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)*, Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
  https://library.slmath.org/books/Book50/files/02AT.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 225E (absolutely continuous functions as indefinite integrals), 225F (integration by parts).
  https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, pp. 313–314, length distance, Definition 4.1 and Lemma 4.2, equations (4–1)–(4–4).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11

**Relationship to the sources:** This is the exact one-form k=1 calibration argument. Only C1 potential and the path-length primitive are needed; convexity and a Riemannian metric are absent.
-/

/-!
# Calibration comparison for the original Finsler path length

A C1 potential whose actual manifold differential is bounded by the given Finsler norm
bounds the length of every C1 curve in its domain. Saturation along a reference curve gives
length minimality among all same-endpoint C1 competitors that stay in the domain.

Curves are C1 within closed time intervals; ordinary endpoint derivatives and speed
integrability are derived or unnecessary. Zero velocities and degenerate intervals are allowed.
All lengths use exactly `ContinuousFinslerNorm.enorm`. No inner product, finite-dimensionality,
or strong convexity is used. The potential and its calibration properties are inputs to this
comparison theorem; this module does not construct a calibration or remove domain containment.
-/

open Bundle Set MeasureTheory Manifold Filter
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

/-- A C1 scalar potential difference is bounded by a continuous nonnegative speed integral.
Only the ordinary derivatives in the open interval are compared. -/
theorem ofReal_sub_le_lintegral_nnreal_of_deriv_le
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} {g : ℝ → ℝ≥0}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ t ∈ Ioo a b, deriv f t ≤ (g t : ℝ)) :
    ENNReal.ofReal (f b - f a) ≤ ∫⁻ t in Icc a b, (g t : ℝ≥0∞) := by
  have hgR : ContinuousOn (fun t ↦ (g t : ℝ)) (Icc a b) :=
    NNReal.continuous_coe.comp_continuousOn hg
  have hgint : IntegrableOn (fun t ↦ (g t : ℝ)) (Icc a b) := hgR.integrableOn_Icc
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (deriv f t) t := by
    intro t ht
    exact ((hf t ⟨ht.1.le, ht.2.le⟩).contDiffAt
      (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero |>.hasDerivAt
  have hle := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hf.continuousOn
    (fun t ht ↦ (hderiv t ht).hasDerivWithinAt) hgint hfg
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hle
  rw [lintegral_coe_eq_integral g hgint]
  exact ENNReal.ofReal_le_ofReal hle

/-- Equality holds when the interior derivative is the continuous nonnegative speed. -/
theorem ofReal_sub_eq_lintegral_nnreal_of_deriv_eq
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} {g : ℝ → ℝ≥0}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ t ∈ Ioo a b, deriv f t = (g t : ℝ)) :
    ENNReal.ofReal (f b - f a) = ∫⁻ t in Icc a b, (g t : ℝ≥0∞) := by
  have hgR : ContinuousOn (fun t ↦ (g t : ℝ)) (Icc a b) :=
    NNReal.continuous_coe.comp_continuousOn hg
  have hgint : IntegrableOn (fun t ↦ (g t : ℝ)) (Icc a b) := hgR.integrableOn_Icc
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (g t : ℝ) t := by
    intro t ht
    rw [← hfg t ht]
    exact ((hf t ⟨ht.1.le, ht.2.le⟩).contDiffAt
      (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero |>.hasDerivAt
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf.continuousOn
    hderiv (hgR.intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at heq
  rw [lintegral_coe_eq_integral g hgint, heq]

namespace ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]

/-- The original Finsler speed of a C1 curve, using its derivative within the closed interval,
is continuous, including at the endpoints. -/
theorem continuousOn_finslerSpeed (F : ContinuousFinslerNorm E M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b)) :
    ContinuousOn (fun t ↦ F.toFun ⟨c t,
      mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1⟩) (Icc a b) := by
  have huniq : UniqueMDiffOn 𝓘(ℝ, ℝ) (Icc a b) := by
    simpa only [uniqueMDiffOn_iff_uniqueDiffOn] using uniqueDiffOn_Icc hab
  have htm := hc.continuousOn_tangentMapWithin (by norm_num) huniq
  have hsection : Continuous (fun t : ℝ ↦ (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    convert (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk (continuous_const (y := (1 : ℝ)))) using 1
    funext t
    rfl
  have hspeed := F.continuous_toFun.comp_continuousOn
    (htm.comp hsection.continuousOn (fun _ ht ↦ ht))
  exact hspeed

omit [IsManifold 𝓘(ℝ, E) 1 M] in
/-- The scalar differential of a C1 function along a C1 manifold curve is its actual
within-interval coordinate derivative, including endpoints of a nondegenerate interval. -/
theorem derivWithin_comp_eq_mfderiv (u : M → ℝ) {U : Set M} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 u U)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hmap : MapsTo c (Icc a b) U) {t : ℝ} (ht : t ∈ Icc a b) :
    derivWithin (u ∘ c) (Icc a b) t =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1) := by
  have hdiffu := (hu.contMDiffAt (hU.mem_nhds (hmap ht))).mdifferentiableAt one_ne_zero
  have hdiffc := hc.mdifferentiableOn one_ne_zero t ht
  have htuniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc a b) t := by
    simpa only [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt] using uniqueDiffOn_Icc hab t ht
  have hchain := mfderiv_comp_mfderivWithin t hdiffu hdiffc htuniq
  have h := congrArg (fun A : ℝ →L[ℝ] ℝ ↦ A 1) hchain
  rw [mfderivWithin_eq_fderivWithin, fderivWithin_derivWithin] at h
  exact h


/-- A C1 calibration bounds every C1 competitor by its original Finsler path length.
No nonzero-speed assumption or ordinary derivative at an endpoint is needed. -/
theorem ofReal_sub_le_pathELength (F : ContinuousFinslerNorm E M)
    {u : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 u U)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x v) (F.toFun ⟨x, v⟩ : ℝ))
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hmap : MapsTo c (Icc a b) U) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ENNReal.ofReal (u (c b) - u (c a)) ≤ Manifold.pathELength 𝓘(ℝ, E) c a b := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  rcases hab.eq_or_lt with rfl | hab
  · simp
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  change ENNReal.ofReal (u (c b) - u (c a)) ≤ ∫⁻ t in Icc a b,
    (F.toFun ⟨c t, mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1⟩ : ℝ≥0∞)
  apply ofReal_sub_le_lintegral_nnreal_of_deriv_le hab.le
    ((hu.comp hc (fun _ ht ↦ hmap ht)).contDiffOn)
    (F.continuousOn_finslerSpeed hab hc)
  intro t ht
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
    derivWithin_comp_eq_mfderiv u hU hu hab hc hmap ⟨ht.1.le, ht.2.le⟩]
  exact hbound _ (hmap ⟨ht.1.le, ht.2.le⟩) _

/-- Along a saturated C1 reference curve, potential increase equals its actual Finsler length. -/
theorem pathELength_eq_of_calibrated (F : ContinuousFinslerNorm E M)
    {u : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 u U)
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hmap : MapsTo c (Icc a b) U)
    (hsat : ∀ t ∈ Ioo a b,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1) =
          (F.toFun ⟨c t, mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1⟩ : ℝ)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    Manifold.pathELength 𝓘(ℝ, E) c a b = ENNReal.ofReal (u (c b) - u (c a)) := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  rcases hab.eq_or_lt with rfl | hab
  · simp
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  change (∫⁻ t in Icc a b,
    (F.toFun ⟨c t, mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1⟩ : ℝ≥0∞)) = _
  symm
  apply ofReal_sub_eq_lintegral_nnreal_of_deriv_eq hab.le
    ((hu.comp hc (fun _ ht ↦ hmap ht)).contDiffOn)
    (F.continuousOn_finslerSpeed hab hc)
  intro t ht
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
    derivWithin_comp_eq_mfderiv u hU hu hab hc hmap ⟨ht.1.le, ht.2.le⟩]
  exact hsat t ht

/-- A saturated reference curve minimizes the original Finsler length among all C1 curves
in the calibration domain with the same oriented endpoints. The parametrization intervals
may differ; comparison curves may have zero speed. -/
theorem pathELength_le_of_calibrated (F : ContinuousFinslerNorm E M)
    {u : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 u U)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x v) (F.toFun ⟨x, v⟩ : ℝ))
    {c d : ℝ → M} {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hd : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 d (Icc a' b'))
    (hcmap : MapsTo c (Icc a b) U) (hdmap : MapsTo d (Icc a' b') U)
    (hstart : c a = d a') (hend : c b = d b')
    (hsat : ∀ t ∈ Ioo a b,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t)
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1) =
          (F.toFun ⟨c t, mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t 1⟩ : ℝ)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    Manifold.pathELength 𝓘(ℝ, E) c a b ≤ Manifold.pathELength 𝓘(ℝ, E) d a' b' := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  rw [F.pathELength_eq_of_calibrated hU hu hab hc hcmap hsat, hstart, hend]
  exact F.ofReal_sub_le_pathELength hU hu hbound hab' hd hdmap

end ContinuousFinslerNorm
end OTSelector.Geometry
