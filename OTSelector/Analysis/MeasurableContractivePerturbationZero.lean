import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import OTSelector.Analysis.ContractivePerturbationZero
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MeasurableContractivePhaseZero.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MeasurableContractivePhaseZero`; the selected original proof blocks follow. -/
section

/-!
Conditions: Jointly measurable Lipschitz fields and operator-valued mobilities satisfying the stated half-contraction bound on the complete target space.

Objects: Measurability of the backward iterates, their canonical fixed zero and the field evaluated there.

Proof detail: Start each backward iteration at zero, preserve joint measurability under composition and pass to the contraction limit.

Sources: Gerald Teschl, Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46); D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106).
Relation: Measurable-parameter contraction corollary; no separately selected random zero is introduced.
-/

/-!
# Measurable inverse zero of the actual small phase perturbation

The canonical inverse zero is the pointwise limit of the backward-map iterates starting
at the deterministic origin. Jointly measurable fields and measurable actual mobility
therefore give a measurable zero, with no separately selected random solution.
-/

open Function Filter MeasureTheory
open scoped Topology NNReal

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [CompleteSpace V] in
/-- Evaluation of the actual measurable mobility on the same actual measurable field is
jointly measurable in the environment and the observation point. -/
theorem measurable_phaseBackwardMap
    {P : Ω→V→V} {R : Ω→V→L[ℝ] V}
    (hP : Measurable (Function.uncurry P)) (hR : Measurable R) :
    Measurable (fun a : Ω×V ↦ phaseBackwardMap (P a.1) (R a.1) a.2) := by
  have heval : Measurable (fun a : (V→L[ℝ] V)×V ↦ a.1 a.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  exact (heval.comp ((hR.comp measurable_fst).prodMk hP)).neg

omit [CompleteSpace V] in
/-- Every deterministic-origin iterate remains measurable in the original environment. -/
theorem measurable_phaseBackwardMap_iterate
    {P : Ω→V→V} {R : Ω→V→L[ℝ] V}
    (hP : Measurable (Function.uncurry P)) (hR : Measurable R) (n : ℕ) :
    Measurable (fun ω ↦ (phaseBackwardMap (P ω) (R ω))^[n] (0:V)) := by
  induction n with
  | zero => simpa only [Function.iterate_zero,Function.id_def] using
      (measurable_const : Measurable (fun _ : Ω ↦ (0:V)))
  | succ n hn =>
      simpa only [Function.iterate_succ_apply',Function.comp_def,id_eq] using
        (measurable_phaseBackwardMap hP hR).comp (measurable_id.prodMk hn)

/-- Joint measurability of the actual field gives measurability of its canonical inverse
zero, using the same actual mobility and the internally proved contracting iterates. -/
theorem measurable_phaseInverseZero
    {P : Ω→V→V} {R : Ω→V→L[ℝ] V} {L : ℝ}
    (hP : Measurable (Function.uncurry P)) (hR : Measurable R)
    (hLip : ∀ω z w, ‖P ω z-P ω w‖≤L*‖z-w‖)
    (hsmall : ∀ω, ‖R ω‖*L≤(1/2:ℝ)) :
    Measurable (fun ω ↦ phaseInverseZero (P ω) (hLip ω) (R ω) (hsmall ω)) := by
  apply measurable_of_tendsto_metrizable (fun n ↦ measurable_phaseBackwardMap_iterate hP hR n)
  apply tendsto_pi_nhds.mpr
  intro ω
  exact (contractingWith_phaseBackwardMap (hLip ω) (hsmall ω)).tendsto_iterate_fixedPoint 0

/-- The canonical field momentum evaluated at that same zero is measurable as well. -/
theorem measurable_field_at_phaseInverseZero
    {P : Ω→V→V} {R : Ω→V→L[ℝ] V} {L : ℝ}
    (hP : Measurable (Function.uncurry P)) (hR : Measurable R)
    (hLip : ∀ω z w, ‖P ω z-P ω w‖≤L*‖z-w‖)
    (hsmall : ∀ω, ‖R ω‖*L≤(1/2:ℝ)) :
    Measurable (fun ω ↦ P ω (phaseInverseZero (P ω) (hLip ω) (R ω) (hsmall ω))) :=
  hP.comp (measurable_id.prodMk (measurable_phaseInverseZero hP hR hLip hsmall))

end OTSelector.Reconstruction

end
end
