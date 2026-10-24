import OTSelector.Analysis.ContractivePerturbationZero
import OTSelector.Analysis.MeasurableContractivePerturbationZero
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ContractivePhaseInverseAt.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ContractivePhaseInverseAt`; the selected original proof blocks follow. -/
section

/-!
Conditions: A Lipschitz field on a complete normed space and a mobility with half-contraction bound, with measurable-parameter assumptions only in the measurable variant.

Objects: The canonical inverse at an arbitrary actual target, its equation, uniqueness, zero-target agreement and joint measurability.

Proof detail: Translate the field by the target, construct its canonical zero and translate back; use uniqueness and measurable contraction iterates.

Sources: Gerald Teschl, Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46); D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106).
Relation: Target-explicit Banach inverse construction. The actual target transforms together with the inverse point.
-/

/-!
# The same phase inverse at an actual target

The inverse at a target a is constructed from the canonical zero of the translated
original field. Its measurability is joint in the environment and target. Keeping the
target explicit is necessary for the actual spatial reroot covariance.
-/

open Function Filter MeasureTheory
open scoped Topology NNReal

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] [NormedSpace ℝ V] in
/-- Translation of the observation point preserves the same actual field Lipschitz bound. -/
theorem phaseField_translate_lipschitz {P : V→V} {L : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖) (a : V) :
    ∀z w, ‖P (a+z)-P (a+w)‖≤L*‖z-w‖ := by
  intro z w
  simpa only [add_sub_add_left_eq_sub] using hP (a+z) (a+w)

/-- The unique inverse at the specified actual target under z↦z+R(P z). -/
def phaseInverseAt (P : V→V) {L : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (R : V→L[ℝ] V) (hsmall : ‖R‖*L≤(1/2:ℝ)) (a : V) : V :=
  a+phaseInverseZero (fun z ↦ P (a+z)) (phaseField_translate_lipschitz hP a) R hsmall

/-- The constructed inverse sends the unchanged actual phase map exactly to its target. -/
theorem phaseInverseAt_eq {P : V→V} {L : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (R : V→L[ℝ] V) (hsmall : ‖R‖*L≤(1/2:ℝ)) (a : V) :
    phaseInverseAt P hP R hsmall a+R (P (phaseInverseAt P hP R hsmall a))=a := by
  have hz := phaseInverseZero_eq (phaseField_translate_lipschitz hP a) R hsmall
  change a+phaseInverseZero _ _ _ _+R (P (a+phaseInverseZero _ _ _ _))=a
  calc
    _ = a+(phaseInverseZero _ _ _ _+R (P (a+phaseInverseZero _ _ _ _))) := by abel
    _ = a := by rw [hz,add_zero]

/-- Every inverse of that same phase map at the same target is the constructed inverse. -/
theorem phaseInverseAt_unique {P : V→V} {L : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (R : V→L[ℝ] V) (hsmall : ‖R‖*L≤(1/2:ℝ)) {a z : V}
    (hz : z+R (P z)=a) : z=phaseInverseAt P hP R hsmall a := by
  have hzero : (z-a)+R (P (a+(z-a)))=0 := by
    have heq : a+(z-a)=z := by abel
    rw [heq]
    calc
      _ = (z+R (P z))-a := by abel
      _ = 0 := by rw [hz,sub_self]
  have h := phaseInverseZero_unique (phaseField_translate_lipschitz hP a) R hsmall hzero
  change z=a+phaseInverseZero _ _ _ _
  rw [←h]
  abel

/-- At target zero this is exactly the already constructed canonical zero. -/
theorem phaseInverseAt_zero {P : V→V} {L : ℝ}
    (hP : ∀z w, ‖P z-P w‖≤L*‖z-w‖)
    (R : V→L[ℝ] V) (hsmall : ‖R‖*L≤(1/2:ℝ)) :
    phaseInverseAt P hP R hsmall 0=phaseInverseZero P hP R hsmall :=
  phaseInverseZero_unique hP R hsmall (phaseInverseAt_eq hP R hsmall 0)

/-- Joint measurability is retained by taking the inverse at a varying actual target. -/
theorem measurable_phaseInverseAt
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {P : Ω→V→V} {R : Ω→V→L[ℝ] V} {L : ℝ}
    (hP : Measurable (Function.uncurry P)) (hR : Measurable R)
    (hLip : ∀ω z w, ‖P ω z-P ω w‖≤L*‖z-w‖)
    (hsmall : ∀ω, ‖R ω‖*L≤(1/2:ℝ)) :
    Measurable (fun a : Ω×V ↦ phaseInverseAt (P a.1) (hLip a.1) (R a.1) (hsmall a.1) a.2) := by
  have hshift : Measurable (Function.uncurry
      (fun a : Ω×V ↦ fun z ↦ P a.1 (a.2+z))) :=
    hP.comp ((measurable_fst.fst).prodMk (measurable_fst.snd.add measurable_snd))
  exact measurable_snd.add (measurable_phaseInverseZero hshift (hR.comp measurable_fst)
    (fun a ↦ phaseField_translate_lipschitz (hLip a.1) a.2) (fun a ↦ hsmall a.1))

end OTSelector.Reconstruction

end
end
