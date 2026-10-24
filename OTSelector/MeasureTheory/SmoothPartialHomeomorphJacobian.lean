import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Order.Compact

/-!
## Lemma skeleton

* **Conditions:** An open partial homeomorphism on a finite-dimensional normed real space, C1 on its source; inverse C1 is required only for derivative invertibility/positive Jacobian/bounds. The map identity requires a measurable source subset.
* **Objects:** Absolute derivative determinant, continuity and positivity, compact upper/lower bounds and its exact Haar density pushforward.
* **Proof detail:** Differentiate the inverse identities to show derivative bijectivity; determinant continuity and compact extrema give bounds. Apply the injective Jacobian change-of-variables theorem to the actual map.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf
* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html

**Relationship to the sources:** C1 partial-homeomorphism specialization of the relative-domain Jacobian theorem. The final density pushforward itself does not require a C1 inverse; the injective partial map and forward C1 suffice.
-/

/-!
# Jacobians of actual smooth coordinate changes

A continuously differentiable open partial homeomorphism with a continuously
differentiable inverse has a positive, continuous absolute derivative determinant
on its source. Its bounds on compact subsets and the Haar change-of-variables
identity concern the actual map and its actual derivative.
-/

open Set MeasureTheory Manifold
open scoped ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The absolute determinant of the actual ordinary derivative of a coordinate change. -/
def partialHomeomorphJacobian (C : OpenPartialHomeomorph E E) (z : E) : ℝ :=
  |(fderiv ℝ C z).det|

/-- Differentiating the actual inverse identities makes the derivative bijective. -/
theorem fderiv_partialHomeomorph_bijective {C : OpenPartialHomeomorph E E}
    (hC : ContDiffOn ℝ 1 C C.source) (hCi : ContDiffOn ℝ 1 C.symm C.target)
    {z : E} (hz : z ∈ C.source) : Function.Bijective (fderiv ℝ C z) := by
  have hd : C.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨hC.differentiableOn_one.mdifferentiableOn,
      hCi.differentiableOn_one.mdifferentiableOn⟩
  simpa only [mfderiv_eq_fderiv] using! hd.mfderiv_bijective hz

/-- The actual Jacobian is continuous on the open coordinate domain. -/
theorem continuousOn_partialHomeomorphJacobian {C : OpenPartialHomeomorph E E}
    (hC : ContDiffOn ℝ 1 C C.source) :
    ContinuousOn (partialHomeomorphJacobian C) C.source := by
  exact (ContinuousLinearMap.continuous_det.comp_continuousOn
    (hC.continuousOn_fderiv_of_isOpen C.open_source le_rfl)).abs

/-- Smooth invertibility gives strictly positive absolute Jacobian at every source point. -/
theorem partialHomeomorphJacobian_pos {C : OpenPartialHomeomorph E E}
    (hC : ContDiffOn ℝ 1 C C.source) (hCi : ContDiffOn ℝ 1 C.symm C.target)
    {z : E} (hz : z ∈ C.source) : 0 < partialHomeomorphJacobian C z := by
  apply abs_pos.mpr
  let A := LinearEquiv.ofBijective (fderiv ℝ C z).toLinearMap
    (fderiv_partialHomeomorph_bijective hC hCi hz)
  exact A.isUnit_det'.ne_zero

/-- Every compact subset of the legal domain has finite positive Jacobian bounds. -/
theorem exists_partialHomeomorphJacobian_bounds {C : OpenPartialHomeomorph E E}
    (hC : ContDiffOn ℝ 1 C C.source) (hCi : ContDiffOn ℝ 1 C.symm C.target)
    {K : Set E} (hK : IsCompact K) (hKC : K ⊆ C.source) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ z ∈ K, a ≤ partialHomeomorphJacobian C z ∧ partialHomeomorphJacobian C z ≤ b := by
  by_cases hne : K.Nonempty
  · have hc := (continuousOn_partialHomeomorphJacobian hC).mono hKC
    obtain ⟨x, hx, _, hmin⟩ := hK.exists_sInf_image_eq_and_le hne hc
    obtain ⟨y, hy, _, hmax⟩ := hK.exists_sSup_image_eq_and_ge hne hc
    exact ⟨_, _, partialHomeomorphJacobian_pos hC hCi (hKC hx),
      partialHomeomorphJacobian_pos hC hCi (hKC hy), fun z hz ↦ ⟨hmin z hz, hmax z hz⟩⟩
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [m.IsAddHaarMeasure]

/-- The actual Jacobian pushes restricted Haar measure to Haar measure on the image. -/
theorem map_withDensity_partialHomeomorphJacobian {C : OpenPartialHomeomorph E E}
    (hC : ContDiffOn ℝ 1 C C.source) {s : Set E} (hs : MeasurableSet s)
    (hsC : s ⊆ C.source) :
    Measure.map C ((m.restrict s).withDensity
      (fun z ↦ ENNReal.ofReal (partialHomeomorphJacobian C z))) = m.restrict (C '' s) := by
  apply map_withDensity_abs_det_fderiv_eq_addHaar m hs.nullMeasurableSet
    (fun z hz ↦ ?_) (C.injOn.mono hsC)
  exact ((hC.differentiableOn_one z (hsC hz)).differentiableAt
    (C.open_source.mem_nhds (hsC hz))).hasFDerivAt.hasFDerivWithinAt

end OTSelector.Geometry
