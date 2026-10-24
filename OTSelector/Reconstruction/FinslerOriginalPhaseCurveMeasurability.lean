import OTSelector.Reconstruction.FinslerOriginalMeasurablePhaseInverse
import OTSelector.MeasureTheory.MeasurableFieldReindex

/-!
# Joint measurability of the original parameterized inverse curve

Any extra measurable time or curve parameter is retained with the unchanged whole scene.
The actual mobility may depend jointly on both. The canonical inverse, its target-zero
specialization and its original momentum are measurable in those same variables.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 80000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Jointly measurable original-scene mobility and targets produce a jointly measurable
actual inverse with every additional time/curve parameter retained. -/
theorem measurable_momentumPhaseInverse_parameters
    {T : Type*} [MeasurableSpace T]
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×T→
      (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ](Fin (finrank ℝ S.covector.ker)→ℝ))
    (hR : Measurable R) (hsmall : ∀a, ‖R a‖*(L:ℝ)≤(1/2:ℝ))
    (target : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×T→
      (Fin (finrank ℝ S.covector.ker)→ℝ)) (htarget : Measurable target) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×T ↦
      D.momentumPhaseInverse cut h L (R a) (hsmall a) a.1 (target a)) := by
  unfold momentumPhaseInverse phaseInverseAt
  apply htarget.add
  apply measurable_phaseInverseZero
  · exact measurable_phaseField_apply (P:=D.momentumPhaseField cut h L)
      (D.measurable_momentumPhaseField hF hw hcut h L)
      (measurable_fst.fst) ((htarget.comp measurable_fst).add measurable_snd)
  · exact hR

/-- In particular the same original field's canonical zero curve is jointly measurable
in its entire original scene and any retained measurable curve parameter. -/
theorem measurable_momentumPhaseZero_parameters
    {T : Type*} [MeasurableSpace T]
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×T→
      (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ](Fin (finrank ℝ S.covector.ker)→ℝ))
    (hR : Measurable R) (hsmall : ∀a, ‖R a‖*(L:ℝ)≤(1/2:ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×T ↦
      phaseInverseZero (D.momentumPhaseField cut h L a.1)
        (D.momentumPhaseField_lipschitz_everywhere cut h L a.1) (R a) (hsmall a)) := by
  have hfield := measurable_phaseField_reindex (P:=D.momentumPhaseField cut h L)
    (D.measurable_momentumPhaseField hF hw hcut h L)
    (r:=fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×T ↦ a.1)
    measurable_fst
  exact measurable_phaseInverseZero hfield hR
    (fun a ↦ D.momentumPhaseField_lipschitz_everywhere cut h L a.1) hsmall

/-- Evaluating the unchanged actual momentum field on that same inverse curve is jointly
measurable, with the complete scene and curve parameter preserved. -/
theorem measurable_momentum_at_phaseZero_parameters
    {T : Type*} [MeasurableSpace T]
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {cut : ℝ} (hcut : cut∈Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (R : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×T→
      (Fin (finrank ℝ S.covector.ker)→ℝ)→L[ℝ](Fin (finrank ℝ S.covector.ker)→ℝ))
    (hR : Measurable R) (hsmall : ∀a, ‖R a‖*(L:ℝ)≤(1/2:ℝ)) :
    Measurable (fun a : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)×T ↦
      D.momentumPhaseField cut h L a.1
        (phaseInverseZero (D.momentumPhaseField cut h L a.1)
          (D.momentumPhaseField_lipschitz_everywhere cut h L a.1) (R a) (hsmall a))) :=
by
  exact measurable_phaseField_apply (P:=D.momentumPhaseField cut h L)
    (D.measurable_momentumPhaseField hF hw hcut h L) measurable_fst
    (D.measurable_momentumPhaseZero_parameters hF hw hcut h L R hR hsmall)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
