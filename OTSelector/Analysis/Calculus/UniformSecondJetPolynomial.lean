import OTSelector.Analysis.Calculus.ParameterizedSecondJetLevel
import OTSelector.Analysis.Calculus.SecondJetPolynomial
import OTSelector.Analysis.Calculus.UniformAmbientSecondJet
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformSecondJetPolynomial.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformSecondJetPolynomial`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual almost-everywhere second jet with the stated compact/Lusin hypotheses.

Objects: A large compact set where the quadratic jet polynomial uniformly approximates both values and gradients.

Proof detail: Select common error-radius sets, derive Hessian symmetry from actual second derivatives and apply Taylor/mean-value estimates uniformly.

Sources: Hassler Whitney, Section 2, Theorem 1 and proof, pp. 144–147, especially uniform first-order compatibility (2.8) (https://msp.org/pjm/1951/1-1/pjm-v1-n1-p15-s.pdf#page=3); Hassler Whitney, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60); Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html).
Relation: Derived compact jet approximation. Polynomial coefficients are actual jets, not freely chosen substitutes.
-/

/-!
# The actual polynomial family on a uniform second-jet core

The large compact subcore is constructed from the original measure and C1
extension. Its explicit polynomial family approximates both the original values
and covectors with one radius for all retained centers and ambient displacements.
Symmetry is derived from the actual second derivative, not assumed for the jets.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The same actual second jets yield one explicit smooth polynomial family with
uniform first- and second-order errors on a large compact subset of the original core. -/
theorem exists_compact_uniform_secondJetPolynomial
    {ν : Measure E} {H : Set E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
          let P := scalarSecondJetPolynomial
            (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
          ‖fderiv ℝ G (x + h) - fderiv ℝ P (x + h)‖ ≤ η * ‖h‖ ∧
          ‖G (x + h) - P (x + h)‖ ≤ η * ‖h‖ ^ 2 := by
  obtain ⟨K, hKH, hK, hloss, hHK, hrem⟩ :=
    exists_compact_uniform_ambient_secondJet hH hνH hG hsecond hHess hε
  refine ⟨K, hKH, hK, hloss, hHK, ?_⟩
  intro η hη
  obtain ⟨r, hr, hbound⟩ := hrem η hη
  refine ⟨r, hr, ?_⟩
  intro x hx h hh
  let B := fderiv ℝ (fderiv ℝ G) x
  let P := scalarSecondJetPolynomial (x, G x, fderiv ℝ G x, B)
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Filter.Eventually.of_forall fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt
  have hsym : ∀ v w : E, B v w = B w v :=
    second_derivative_symmetric_of_eventually hfirst (hsecond x (hKH hx)).hasFDerivAt
  have hDP : fderiv ℝ P (x + h) = fderiv ℝ G x + B h := by
    simpa only [P, scalarSecondJetPolynomial, add_sub_cancel_left] using
      (hasFDerivAt_secondJetPolynomial x (G x) (fderiv ℝ G x) B hsym (x + h)).fderiv
  have hv : G (x + h) - P (x + h) =
      G (x + h) - G x - fderiv ℝ G x h - (1 / 2 : ℝ) * B h h := by
    dsimp only [P, scalarSecondJetPolynomial, secondJetPolynomial]
    simp only [add_sub_cancel_left]
    ring
  obtain ⟨hderiv, hvalue⟩ := hbound x hx h hh
  change ‖fderiv ℝ G (x + h) - fderiv ℝ P (x + h)‖ ≤ η * ‖h‖ ∧
    ‖G (x + h) - P (x + h)‖ ≤ η * ‖h‖ ^ 2
  constructor
  · simpa only [hDP, sub_add_eq_sub_sub, B] using hderiv
  · rw [hv]
    exact hvalue

end OTSelector.Geometry

end
end
