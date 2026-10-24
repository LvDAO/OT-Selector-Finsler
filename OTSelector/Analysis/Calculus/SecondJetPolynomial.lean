import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Analysis.Calculus.SecondJetPolynomial

Conditions: An arbitrary prescribed value, continuous linear first differential and symmetric continuous bilinear second differential, or an actual twice Fréchet differentiable jet.

Objects: An explicit smooth quadratic polynomial realizing the same second jet.

Proof detail: Define value plus first-order term plus one half the diagonal quadratic term. Compute its first and second derivatives; for an actual second derivative use its symmetry and instantiate the polynomial.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=60): Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives).

Source relation: Polynomial construction is local algebra. The book’s C2 symmetry theorem is background; Lean’s actual twice-Fréchet-differentiable-at-one-point formulation is more general and is not attributed verbatim.
-/

/-!
# A smooth polynomial realizing one actual second jet

The explicit quadratic polynomial realizes any symmetric bounded second jet. For an
actual function differentiable in a neighborhood with a derivative differentiable at
just the central point, mathlib's pointwise Schwarz theorem derives symmetry. No C2
neighborhood, Whitney extension, or new regularity assumption on the original function
is needed to construct a globally smooth function with the same value and two derivatives.
-/

open Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit scalar polynomial realizing the value, covector and symmetric second jet. -/
def secondJetPolynomial (x : E) (value : ℝ) (p : E →L[ℝ] ℝ)
    (B : E →L[ℝ] (E →L[ℝ] ℝ)) (y : E) : ℝ :=
  value + p (y - x) + (1 / 2 : ℝ) * B (y - x) (y - x)

/-- The jet polynomial is smooth on the entire model vector space. -/
theorem contDiff_secondJetPolynomial (x : E) (value : ℝ) (p : E →L[ℝ] ℝ)
    (B : E →L[ℝ] (E →L[ℝ] ℝ)) : ContDiff ℝ ∞ (secondJetPolynomial x value p B) := by
  have hs : ContDiff ℝ ∞ (fun y : E ↦ y - x) := contDiff_id.sub contDiff_const
  exact (contDiff_const.add (p.contDiff.comp hs)).add
    (contDiff_const.mul ((B.contDiff.comp hs).clm_apply hs))

/-- The jet polynomial takes the specified central value. -/
theorem secondJetPolynomial_self (x : E) (value : ℝ) (p : E →L[ℝ] ℝ)
    (B : E →L[ℝ] (E →L[ℝ] ℝ)) : secondJetPolynomial x value p B x = value := by
  simp [secondJetPolynomial]

/-- Symmetry gives the exact first derivative of the jet polynomial at every point. -/
theorem hasFDerivAt_secondJetPolynomial (x : E) (value : ℝ) (p : E →L[ℝ] ℝ)
    (B : E →L[ℝ] (E →L[ℝ] ℝ)) (hB : ∀ v w : E, B v w = B w v) (y : E) :
    HasFDerivAt (secondJetPolynomial x value p B) (p + B (y - x)) y := by
  have hs := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
  have hquad := ((B.hasFDerivAt.comp y hs).clm_apply hs).const_mul (1 / 2 : ℝ)
  have h := ((p.hasFDerivAt.comp y hs).const_add value).add hquad
  convert! h using 1
  ext v
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, Function.comp_apply, id_eq]
  rw [hB v (y - x)]
  ring

/-- The actual first derivative of the jet polynomial has derivative exactly the
prescribed symmetric bilinear operator, at every point. -/
theorem hasFDerivAt_fderiv_secondJetPolynomial (x : E) (value : ℝ)
    (p : E →L[ℝ] ℝ) (B : E →L[ℝ] (E →L[ℝ] ℝ))
    (hB : ∀ v w : E, B v w = B w v) (y : E) :
    HasFDerivAt (fderiv ℝ (secondJetPolynomial x value p B)) B y := by
  have heq : fderiv ℝ (secondJetPolynomial x value p B) = fun z ↦ p + B (z - x) :=
    funext (fun z ↦ (hasFDerivAt_secondJetPolynomial x value p B hB z).fderiv)
  rw [heq]
  convert! (B.hasFDerivAt.comp y ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const x)).const_add p
    using 1

/-- Any symmetric bounded second jet has an explicit globally smooth representative. -/
theorem exists_smooth_secondJet_of_symmetric (x : E) (value : ℝ)
    (p : E →L[ℝ] ℝ) (B : E →L[ℝ] (E →L[ℝ] ℝ))
    (hB : ∀ v w : E, B v w = B w v) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = value ∧
      HasFDerivAt P p x ∧ HasFDerivAt (fderiv ℝ P) B x := by
  refine ⟨secondJetPolynomial x value p B, contDiff_secondJetPolynomial x value p B,
    secondJetPolynomial_self x value p B, ?_,
    hasFDerivAt_fderiv_secondJetPolynomial x value p B hB x⟩
  simpa only [sub_self, map_zero, add_zero] using
    hasFDerivAt_secondJetPolynomial x value p B hB x

/-- If the actual first derivative exists near the center and is differentiable only
at that point, a globally smooth polynomial matches its actual value and second jet.
Schwarz symmetry follows from those assumptions; no neighborhood C2 condition is imposed. -/
theorem exists_smooth_matching_secondJet {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {x : E} {B : E →L[ℝ] (E →L[ℝ] ℝ)}
    (hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hsecond : HasFDerivAt f' B x) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = f x ∧
      HasFDerivAt P (f' x) x ∧ HasFDerivAt (fderiv ℝ P) B x ∧
      fderiv ℝ P x = fderiv ℝ f x ∧
      fderiv ℝ (fderiv ℝ P) x = fderiv ℝ (fderiv ℝ f) x := by
  have hB : ∀ v w : E, B v w = B w v :=
    second_derivative_symmetric_of_eventually hfirst hsecond
  obtain ⟨P, hP, hval, hD, hD₂⟩ := exists_smooth_secondJet_of_symmetric x (f x) (f' x) B hB
  have hactual : fderiv ℝ f =ᶠ[𝓝 x] f' := hfirst.mono (fun _ h ↦ h.fderiv)
  have hf₂ : HasFDerivAt (fderiv ℝ f) B x :=
    hsecond.congr_of_eventuallyEq hactual
  exact ⟨P, hP, hval, hD, hD₂, hD.fderiv.trans hfirst.self_of_nhds.fderiv.symm,
    hD₂.fderiv.trans hf₂.fderiv.symm⟩

end OTSelector.Geometry
