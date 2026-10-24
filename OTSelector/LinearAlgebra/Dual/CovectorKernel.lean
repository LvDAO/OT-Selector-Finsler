import OTSelector.Analysis.NormedSpace.CovectorSplitting
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CovectorKernelDuality.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CovectorKernelDuality`; the selected original proof blocks follow. -/
section

/-!
Conditions: A covector pairs nontrivially with a transverse vector; compressed positivity/inversion uses the explicitly symmetric positive operator and radial identity.

Objects: Projection onto the covector kernel, dual lift, compressed form and inverse identity.

Proof detail: Verify projection and lift by evaluation, transport symmetry/positivity, then prove the inverse equation directly from HC=id and Hv=p.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48).
Relation: Elementary kernel/dual algebra without an implicit inner-product identification of vectors and covectors.
-/

/-!
# Dual coordinates for a covector kernel

A covector nonzero on a vector gives a projection onto its kernel along that vector.
A functional on the kernel extends to the ambient space by this projection, vanishing
on the chosen vector. Compressing an ambient dual-to-vector map uses both this dual
extension and the vector projection, without an inner product.

For a symmetric form H with H(v)=p, an actual right inverse C carries these extended
functionals into ker p. Its compression is therefore the inverse restricted form.
This states the compatibility explicitly; restriction and inversion are not presumed
to commute. Positivity and symmetry of C transfer to its compression.
-/

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Projection onto the covector kernel along a vector paired nontrivially with it. -/
def covectorKernelProjection (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) : E →L[ℝ] p.ker :=
  (ContinuousLinearMap.fst ℝ p.ker ℝ).comp (covectorSplitting p v hv).symm.toContinuousLinearMap

/-- The actual projected vector is obtained by subtracting its radial component. -/
theorem covectorKernelProjection_coe (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) (x : E) :
    (covectorKernelProjection p v hv x : E) = x - (p x / p v) • v :=
  covectorSplitting_symm_fst p v hv x

/-- The projection fixes every vector already in the covector kernel. -/
@[simp] theorem covectorKernelProjection_subtype
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) (w : p.ker) :
    covectorKernelProjection p v hv (w : E) = w := by
  apply Subtype.ext
  rw [covectorKernelProjection_coe, show p (w : E) = 0 from w.property]
  simp

/-- The projection annihilates the chosen radial vector. -/
@[simp] theorem covectorKernelProjection_radial
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) :
    covectorKernelProjection p v hv v = 0 := by
  apply Subtype.ext
  simp [covectorKernelProjection_coe, hv]

/-- Extend kernel functionals by zero in the chosen radial direction. -/
def covectorKernelDualLift (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) :
    (p.ker →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E p.ker ℝ).flip (covectorKernelProjection p v hv)

/-- Evaluation of the dual extension is evaluation after the kernel projection. -/
theorem covectorKernelDualLift_apply (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    (η : p.ker →L[ℝ] ℝ) (x : E) :
    covectorKernelDualLift p v hv η x = η (covectorKernelProjection p v hv x) := rfl

/-- The extension restricts to the original kernel functional. -/
@[simp] theorem covectorKernelDualLift_subtype (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    (η : p.ker →L[ℝ] ℝ) (w : p.ker) :
    covectorKernelDualLift p v hv η (w : E) = η w := by
  rw [covectorKernelDualLift_apply, covectorKernelProjection_subtype]

/-- The dual extension vanishes on the radial vector. -/
@[simp] theorem covectorKernelDualLift_radial (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    (η : p.ker →L[ℝ] ℝ) : covectorKernelDualLift p v hv η v = 0 := by
  rw [covectorKernelDualLift_apply, covectorKernelProjection_radial, map_zero]

/-- Extension is injective because restriction recovers every kernel functional. -/
theorem covectorKernelDualLift_injective (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) :
    Function.Injective (covectorKernelDualLift p v hv) := by
  intro η ξ h
  ext w
  simpa only [covectorKernelDualLift_subtype] using
    congrArg (fun q : E →L[ℝ] ℝ ↦ q (w : E)) h

/-- Compress an ambient dual-to-vector map using the dual lift and kernel projection. -/
def covectorKernelCompression (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    (C : (E →L[ℝ] ℝ) →L[ℝ] E) : (p.ker →L[ℝ] ℝ) →L[ℝ] p.ker :=
  (covectorKernelProjection p v hv).comp (C.comp (covectorKernelDualLift p v hv))

/-- Positive ambient dual-to-vector maps remain positive after this compression. -/
theorem covectorKernelCompression_pos (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {C : (E →L[ℝ] ℝ) →L[ℝ] E} (hC : ∀ q : E →L[ℝ] ℝ, q ≠ 0 → 0 < q (C q))
    {η : p.ker →L[ℝ] ℝ} (hη : η ≠ 0) :
    0 < η (covectorKernelCompression p v hv C η) := by
  apply hC (covectorKernelDualLift p v hv η)
  intro he
  apply hη
  apply covectorKernelDualLift_injective p v hv
  simpa only [map_zero] using he

/-- Canonical symmetry is preserved by dual extension and vector projection. -/
theorem covectorKernelCompression_symm (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {C : (E →L[ℝ] ℝ) →L[ℝ] E} (hC : ∀ q r : E →L[ℝ] ℝ, r (C q) = q (C r))
    (η ξ : p.ker →L[ℝ] ℝ) :
    ξ (covectorKernelCompression p v hv C η) = η (covectorKernelCompression p v hv C ξ) :=
  hC (covectorKernelDualLift p v hv η) (covectorKernelDualLift p v hv ξ)

/-- A right inverse of a symmetric form with H(v)=p maps lifted covectors into ker p. -/
theorem covectorKernelCompression_coe_of_inverse
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {H : E →L[ℝ] (E →L[ℝ] ℝ)} {C : (E →L[ℝ] ℝ) →L[ℝ] E}
    (hH : ∀ u w, H u w = H w u) (hrad : H v = p) (hHC : ∀ q, H (C q) = q)
    (η : p.ker →L[ℝ] ℝ) :
    (covectorKernelCompression p v hv C η : E) = C (covectorKernelDualLift p v hv η) := by
  have hp : p (C (covectorKernelDualLift p v hv η)) = 0 := by
    calc
      p (C (covectorKernelDualLift p v hv η)) =
          H v (C (covectorKernelDualLift p v hv η)) := congrArg
            (fun q : E →L[ℝ] ℝ ↦ q (C (covectorKernelDualLift p v hv η))) hrad.symm
      _ = H (C (covectorKernelDualLift p v hv η)) v := hH _ _
      _ = covectorKernelDualLift p v hv η v := congrArg (fun q : E →L[ℝ] ℝ ↦ q v) (hHC _)
      _ = 0 := covectorKernelDualLift_radial p v hv η
  change (covectorKernelProjection p v hv (C (covectorKernelDualLift p v hv η)) : E) = _
  rw [covectorKernelProjection_coe, hp]
  simp

/-- The compressed right inverse inverts the form restricted to the actual covector kernel. -/
theorem covectorKernelCompression_inverse
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {H : E →L[ℝ] (E →L[ℝ] ℝ)} {C : (E →L[ℝ] ℝ) →L[ℝ] E}
    (hH : ∀ u w, H u w = H w u) (hrad : H v = p) (hHC : ∀ q, H (C q) = q)
    (η : p.ker →L[ℝ] ℝ) (w : p.ker) :
    H (covectorKernelCompression p v hv C η : E) (w : E) = η w := by
  rw [covectorKernelCompression_coe_of_inverse p v hv hH hrad hHC,
    hHC, covectorKernelDualLift_subtype]

end OTSelector.Geometry

end
end
