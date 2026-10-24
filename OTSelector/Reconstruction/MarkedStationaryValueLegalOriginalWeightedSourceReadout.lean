import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoCycleDefect
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalPathWindowReadout

/-!
# The exact original weighted mean read through a physical source window

The signed physical edge-cost observable is precisely the already proved
source-window Campbell readout. Its expectation equals the Haar window mass
times the original weighted Palm value, with actual integrability included.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

/-- The unchanged original weighted edge cost in an actual physical source window. -/
def originalWeightedSourceReadout {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (w : (Fin q → ℝ) → ℝ) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ∫ e, w e.1.1 * originalWeightedEdgeCost kin g t e
    ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))

/-- The physical source-window observable is literally the same actual
Campbell kernel readout, with original paired clocks and full displacement. -/
theorem originalWeightedSourceReadout_eq_pathWindowReadout {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (w : (Fin q → ℝ) → ℝ) (hw : Measurable w)
    (s : LegalMarkedOptimalInputScene q) :
    originalWeightedSourceReadout kin g t w s =
      legalMarkedPathWindowReadout q (fun _ ↦ 0) w
        (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) s := by
  have hf : Measurable (fun m : PhysicalPairPalmMark (Fin q) ↦
      kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) :=
    hk.add ((hg.comp measurable_fst).const_mul t)
  have hm : Measurable (fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      w (p.1 + 0) * (kin p.2.1.1 p.2.1.2 p.2.2 + t * g p.2.1.1 p.2.1.2)) :=
    (hw.comp (measurable_fst.add measurable_const)).mul (hf.comp measurable_snd)
  symm
  change (∫ p, w (p.1 + 0) *
    (kin p.2.1.1 p.2.1.2 p.2.2 + t * g p.2.1.1 p.2.1.2)
      ∂physicalScenePairKernel s.1) = _
  rw [physicalScenePairKernel_apply,
    integral_map measurable_physicalPairAnchor.aemeasurable hm.aestronglyMeasurable]
  simp only [physicalPairAnchor, add_zero, originalWeightedSourceReadout,
    originalWeightedEdgeCost]

/-- The original weighted minimum is exactly the expected signed physical
cost per Haar source volume; no local uniform-integrability premise is supplied. -/
theorem LegalWeightedStationaryPoissonMatching.weightedSourceReadout_integrable_and_integral
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ} (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {w : (Fin q → ℝ) → ℝ} (hwm : Measurable w)
    (hw : Integrable w (volume : Measure (Fin q → ℝ))) :
    Integrable (originalWeightedSourceReadout kin g t w)
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, originalWeightedSourceReadout kin g t w s
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
        (∫ x, w x ∂(volume : Measure (Fin q → ℝ))) * M.value t := by
  have hfi : Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦
      kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) (legalMarkedJointPalm q M.law) :=
    M.kinetic_integrable.add (M.probe_integrable.const_mul t)
  have hread := M.pathWindowReadout_integrable_and_integral
    (fun _ ↦ 0) measurable_const hw hfi
  have heq : originalWeightedSourceReadout kin g t w =
      legalMarkedPathWindowReadout q (fun _ ↦ 0) w
        (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) :=
    funext fun s ↦ originalWeightedSourceReadout_eq_pathWindowReadout kin hk g hg t w hwm s
  rw [heq]
  have hvalue : (∫ m, kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
      ∂legalMarkedJointPalm q M.law) = M.value t := by
    rw [integral_add M.kinetic_integrable (M.probe_integrable.const_mul t), integral_const_mul]
    rfl
  simpa only [smul_eq_mul, hvalue] using hread

end OTSelector.Reconstruction
