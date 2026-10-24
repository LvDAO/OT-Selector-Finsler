import OTSelector.Analysis.ContractivePerturbationInverse
import OTSelector.Analysis.ContractivePerturbationZero
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ContractivePhaseInverseCovariance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ContractivePhaseInverseCovariance`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two small-Lipschitz phase maps have the stated exact agreement or affine-conjugacy identity, with both actual targets explicit.

Objects: Recoding invariance and affine, translation and linear-isometry covariance of the canonical inverse.

Proof detail: Show the transformed inverse point solves the transformed target equation and apply uniqueness.

Sources: Gerald Teschl, Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Uniqueness corollary. The target-zero inverse is not asserted to be a translation-covariant spatial point.
-/

/-!
# Covariance of the same canonical phase inverse

Uniqueness gives recoding invariance and exact covariance under affine phase changes.
Spatial translations act on the actual target as well as on the inverse point; the fixed
target-zero inverse is not asserted to be a translation-covariant spatial point.
-/

open Function
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Equal actual phase maps give identical canonical inverses, independently of field
representations, certificates, or original atom codes. -/
theorem phaseInverseAt_eq_of_phaseMap_eq
    {P Q : V→V} {L L' : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (hQ : ∀z w, ‖Q z-Q w‖≤L'*‖z-w‖)
    (R R' : V→L[ℝ] V)
    (hsmall : ‖R‖*L≤(1/2:ℝ)) (hsmall' : ‖R'‖*L'≤(1/2:ℝ))
    (hphase : ∀z, R (P z)=R' (Q z)) (a : V) :
    phaseInverseAt P hP R hsmall a=phaseInverseAt Q hQ R' hsmall' a := by
  apply phaseInverseAt_unique hQ R' hsmall'
  rw [←hphase]
  exact phaseInverseAt_eq hP R hsmall a

/-- Equal actual phase maps also give identical canonical zeros. -/
theorem phaseInverseZero_eq_of_phaseMap_eq
    {P Q : V→V} {L L' : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (hQ : ∀z w, ‖Q z-Q w‖≤L'*‖z-w‖)
    (R R' : V→L[ℝ] V)
    (hsmall : ‖R‖*L≤(1/2:ℝ)) (hsmall' : ‖R'‖*L'≤(1/2:ℝ))
    (hphase : ∀z, R (P z)=R' (Q z)) :
    phaseInverseZero P hP R hsmall=phaseInverseZero Q hQ R' hsmall' := by
  simpa only [phaseInverseAt_zero] using
    phaseInverseAt_eq_of_phaseMap_eq hP hQ R R' hsmall hsmall' hphase 0

/-- A commuting actual affine phase change transports the unique inverse and its target. -/
theorem phaseInverseAt_affine_covariant
    {P : V→V} {Q : W→W} {L L' : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (hQ : ∀z w, ‖Q z-Q w‖≤L'*‖z-w‖)
    (R : V→L[ℝ] V) (R' : W→L[ℝ] W)
    (hsmall : ‖R‖*L≤(1/2:ℝ)) (hsmall' : ‖R'‖*L'≤(1/2:ℝ))
    (A : V→L[ℝ] W) (b : W)
    (hphase : ∀z, R' (Q (A z+b))=A (R (P z))) (a : V) :
    phaseInverseAt Q hQ R' hsmall' (A a+b)=A (phaseInverseAt P hP R hsmall a)+b := by
  symm
  apply phaseInverseAt_unique hQ R' hsmall'
  rw [hphase]
  calc
    _ = A (phaseInverseAt P hP R hsmall a+R (P (phaseInverseAt P hP R hsmall a)))+b := by
      rw [A.map_add]
      abel
    _ = A a+b := by rw [phaseInverseAt_eq]

/-- In particular, the original spatial reroot convention transports the actual target
by the same subtraction as the actual inverse point. -/
theorem phaseInverseAt_translate_covariant
    {P Q : V→V} {L L' : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (hQ : ∀z w, ‖Q z-Q w‖≤L'*‖z-w‖)
    (R : V→L[ℝ] V)
    (hsmall : ‖R‖*L≤(1/2:ℝ)) (hsmall' : ‖R‖*L'≤(1/2:ℝ))
    (v : V) (hshift : ∀z, Q (z-v)=P z) (a : V) :
    phaseInverseAt Q hQ R hsmall' (a-v)=phaseInverseAt P hP R hsmall a-v := by
  symm
  apply phaseInverseAt_unique hQ R hsmall'
  rw [hshift]
  calc
    _ = (phaseInverseAt P hP R hsmall a+R (P (phaseInverseAt P hP R hsmall a)))-v := by abel
    _ = a-v := by rw [phaseInverseAt_eq]

/-- Linear isometries preserve the same canonical inverse whenever the actual fields
and mobilities have the corresponding physical phase covariance. -/
theorem phaseInverseAt_linearIsometry_covariant
    {P : V→V} {Q : W→W} {L L' : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (hQ : ∀z w, ‖Q z-Q w‖≤L'*‖z-w‖)
    (R : V→L[ℝ] V) (R' : W→L[ℝ] W)
    (hsmall : ‖R‖*L≤(1/2:ℝ)) (hsmall' : ‖R'‖*L'≤(1/2:ℝ))
    (A : V≃ₗᵢ[ℝ] W) (hphase : ∀z, R' (Q (A z))=A (R (P z))) (a : V) :
    phaseInverseAt Q hQ R' hsmall' (A a)=A (phaseInverseAt P hP R hsmall a) := by
  symm
  apply phaseInverseAt_unique hQ R' hsmall'
  rw [hphase,←A.map_add,phaseInverseAt_eq]

end OTSelector.Reconstruction

end
end
