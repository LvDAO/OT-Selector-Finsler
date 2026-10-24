import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Analysis.Calculus.MixedFlowJetMatching

Conditions: A smooth flow and two seed/clock pairs whose values and actual first derivatives agree in the stated mixed ambient/within-set sense.

Objects: Equality of the actual first jets of the two clock-shifted flow compositions.

Proof detail: Apply the chain rule to position and clock parameters, then substitute matching seed and clock values/differentials.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.

Source relation: Chain-rule adapter; no density, measure, or probabilistic premise is introduced.
-/

/-!
# Mixed ambient and within-set jets under a parameter-dependent flow clock

A rough seed and clock need only be differentiable within the allowed set. The
normal seed and clock have ordinary derivatives. Their matching first jets therefore
propagate to the actual ambient derivative of the normal composite, without any
unique-differentiability or density assumption on the allowed set.
-/

open Set

noncomputable section
namespace OTSelector.Geometry

variable {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Matching mixed first jets propagate to the actual ambient derivative of the normal
flow composite. The rough composite has this same derivative within an arbitrary set;
no uniqueness of within-set derivatives is used. -/
theorem flow_comp_sub_clock_same_firstJet_mixed {Φ : W × ℝ → Z}
    {X Y : V → W} {f g : V → ℝ} {s : Set V} {x : V}
    {D : V →L[ℝ] W} {a : V →L[ℝ] ℝ} (r : ℝ)
    (hX : HasFDerivWithinAt X D s x) (hY : HasFDerivAt Y D x)
    (hf : HasFDerivWithinAt f a s x) (hg : HasFDerivAt g a x)
    (hseed : X x = Y x) (hclock : f x = g x)
    (hΦ : DifferentiableAt ℝ Φ (Y x, r - g x)) :
    Φ (X x, r - f x) = Φ (Y x, r - g x) ∧
      HasFDerivAt (fun y ↦ Φ (Y y, r - g y))
        (fderiv ℝ (fun y ↦ Φ (Y y, r - g y)) x) x ∧
      HasFDerivWithinAt (fun y ↦ Φ (X y, r - f y))
        (fderiv ℝ (fun y ↦ Φ (Y y, r - g y)) x) s x := by
  have hnormal : HasFDerivAt (fun y ↦ Φ (Y y, r - g y))
      ((fderiv ℝ Φ (Y x, r - g x)).comp (D.prod (-a))) x :=
    hΦ.hasFDerivAt.comp x (hY.prodMk (hg.const_sub r))
  have hΦrough : HasFDerivAt Φ (fderiv ℝ Φ (Y x, r - g x)) (X x, r - f x) := by
    rw [hseed, hclock]
    exact hΦ.hasFDerivAt
  have hrough := hΦrough.comp_hasFDerivWithinAt x (hX.prodMk (hf.const_sub r))
  refine ⟨by rw [hseed, hclock], ?_, ?_⟩
  · rw [hnormal.fderiv]
    exact hnormal
  · rw [hnormal.fderiv]
    exact hrough

end OTSelector.Geometry
