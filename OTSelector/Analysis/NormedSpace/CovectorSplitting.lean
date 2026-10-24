import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
## Lemma skeleton

* **Conditions:** A real normed space E, continuous covector p and vector v with p(v) nonzero; no finite dimension, completeness or inner product is required.
* **Objects:** The continuous linear equivalence ker(p) × R ≃ E sending (w,t) to w+t*v, with explicit inverse and an invertible derivative.
* **Proof detail:** Recover t=p(x)/p(v), then w=x-t*v lies in the kernel. Prove the two formulas are inverse and continuous; the linear map is its own Fréchet derivative.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 6.2, Lemma 6.2 and proof, pp. 190–191 (straightening out of vector fields).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=201
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55.
  https://www.jirka.org/ra/realanal2.pdf#page=55

**Relationship to the sources:** This is the explicit normed-space splitting underlying a transverse affine section. It is an elementary generalization of the linear coordinate/block step in the cited flow-box and implicit-function proofs, not a claimed same-form numbered theorem.
-/

/-!
# Splitting a model space by a covector

A covector nonzero on a chosen vector splits a real normed space into its kernel and
the line parameter in that vector's direction. Both coordinate maps are explicit,
and the resulting continuous linear equivalence supplies an invertible derivative.
No finite-dimensional, completeness, or inner product assumption is required.
-/

noncomputable section

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The kernel of a covector and a transverse vector give continuous linear coordinates. -/
def covectorSplitting (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) :
    (p.ker × ℝ) ≃L[ℝ] E := by
  let q : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight ((p v)⁻¹ • v)
  have hq : Function.RightInverse q p := by
    intro t
    simp [q, hv]
  exact ((ContinuousLinearEquiv.refl ℝ p.ker).prodCongr
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (p v) hv))).trans
    ((ContinuousLinearEquiv.prodComm ℝ p.ker ℝ).trans
      (ContinuousLinearEquiv.equivOfRightInverse p q hq).symm)

/-- The splitting sends a kernel vector and a scalar to their linear sum. -/
@[simp] theorem covectorSplitting_apply
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) (w : p.ker) (t : ℝ) :
    covectorSplitting p v hv (w, t) = (w : E) + t • v := by
  simp [covectorSplitting, smul_smul, hv, add_comm]

/-- The transverse coordinate is evaluation by the covector divided by its value on `v`. -/
@[simp] theorem covectorSplitting_symm_snd
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) (x : E) :
    ((covectorSplitting p v hv).symm x).2 = p x / p v := by
  simp [covectorSplitting, div_eq_mul_inv]

/-- The kernel component subtracts the transverse component from the original vector. -/
@[simp] theorem covectorSplitting_symm_fst
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) (x : E) :
    (((covectorSplitting p v hv).symm x).1 : E) = x - (p x / p v) • v := by
  simp [covectorSplitting, div_eq_mul_inv, smul_smul]

/-- The splitting's linear map is the sum of the kernel inclusion and transverse line map. -/
theorem covectorSplitting_toContinuousLinearMap
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) :
    (covectorSplitting p v hv).toContinuousLinearMap =
      p.ker.subtypeL.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight v) := by
  apply ContinuousLinearMap.ext
  rintro ⟨w, t⟩
  simp

/-- The explicit coordinate map has the splitting equivalence as its actual derivative. -/
theorem hasFDerivAt_covectorSplitting
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) (z : p.ker × ℝ) :
    HasFDerivAt (fun q : p.ker × ℝ ↦ (q.1 : E) + q.2 • v)
      (covectorSplitting p v hv).toContinuousLinearMap z := by
  rw [covectorSplitting_toContinuousLinearMap]
  exact (p.ker.subtypeL.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight v)).hasFDerivAt

/-- The kernel inclusion together with a transverse line has an invertible derivative. -/
theorem isInvertible_covectorSplitting_coprod
    (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0) :
    (p.ker.subtypeL.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight v)).IsInvertible := by
  rw [← covectorSplitting_toContinuousLinearMap p v hv]
  exact ContinuousLinearMap.isInvertible_equiv

end OTSelector.Geometry
