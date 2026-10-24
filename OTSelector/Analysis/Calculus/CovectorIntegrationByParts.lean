import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
## Lemma skeleton

* **Conditions:** C1 covector and vector curves on an open interval containing a compact integration interval.
* **Objects:** The integral of p(t) applied to W′(t).
* **Proof detail:** Apply the derivative product rule to the scalar pairing p(t)(W(t)), integrate, and isolate the term.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 225E (absolutely continuous functions as indefinite integrals), 225F (integration by parts).
  https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** Fremlin states scalar integration by parts; continuous bilinear covector evaluation gives the normed-space version as a direct local corollary.
-/

/-!
# Integration by parts for the actual covector-vector pairing

For C1 covector and vector curves on an open neighborhood of a compact time interval,
the genuine ordinary derivatives satisfy the scalar integration-by-parts identity.
Continuity and interval integrability follow from the C1 hypotheses. The model space
is an arbitrary real normed space; no inner product, completeness, finite dimension,
supplied derivatives or derivative bounds are required.
-/

open Set MeasureTheory
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrate the actual covector-vector derivative pairing by parts. All integrability
conditions are derived from C1 regularity on the given open time neighborhood. -/
theorem integral_covector_deriv_eq_boundary_sub_integral_deriv
    {p : ℝ → E →L[ℝ] ℝ} {W : ℝ → E} {I : Set ℝ} {a b : ℝ}
    (hI : IsOpen I) (hab : a ≤ b) (hsub : Icc a b ⊆ I)
    (hp : ContDiffOn ℝ 1 p I) (hW : ContDiffOn ℝ 1 W I) :
    (∫ t in a..b, p t (deriv W t)) =
      p b (W b) - p a (W a) - ∫ t in a..b, deriv p t (W t) := by
  have hp' := hp.continuousOn_deriv_of_isOpen hI le_rfl
  have hW' := hW.continuousOn_deriv_of_isOpen hI le_rfl
  have hleft : IntervalIntegrable (fun t ↦ deriv p t (W t)) volume a b :=
    ((hp'.clm_apply hW.continuousOn).mono hsub).intervalIntegrable_of_Icc hab
  have hright : IntervalIntegrable (fun t ↦ p t (deriv W t)) volume a b :=
    ((hp.continuousOn.clm_apply hW').mono hsub).intervalIntegrable_of_Icc hab
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s ↦ p s (W s)) (deriv p t (W t) + p t (deriv W t)) t := by
    intro t ht
    have htI : t ∈ I := hsub ((uIcc_of_le hab) ▸ ht)
    exact ((hp.contDiffAt (hI.mem_nhds htI)).differentiableAt_one.hasDerivAt).clm_apply
      ((hW.contDiffAt (hI.mem_nhds htI)).differentiableAt_one.hasDerivAt)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hleft.add hright)
  rw [intervalIntegral.integral_add hleft hright] at hFTC
  linarith

end OTSelector.Geometry
