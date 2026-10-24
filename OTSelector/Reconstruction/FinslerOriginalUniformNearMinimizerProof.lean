import OTSelector.Reconstruction.FinslerOriginalActualLaneSqueezeProof

/-!
# The uniform near-minimizer bound: competitor form and independence witness

The residual of batch108 is `ZeroTiltNearMinimizerReadoutUniform datum p`.  This file

1. recasts it in the exact **competitor-comparison** form a minimality argument must
   produce: every admissible matching whose probe exceeds the limit readout by more than δ
   must have frozen energy strictly bigger than `Iw 0 + δ`
   (`zeroTiltNearMinimizerReadoutUniform_iff_probeExcessForcesEnergyExcess`).  This is
   logically the same content, but it displays precisely the inequality a competitor
   construction has to prove: a probe-exceeding matching cannot be almost kinetic-minimal.
2. proves that this inequality is **NOT derivable from the installed datum structure**:
   `counterDatum` is a legitimate `StationaryPressureDatum` (K = 0, P = 1, Cw = C2 = univ,
   competitor K = 0 <= Cb = 0, probe bound G = 1) for which the uniform bound fails
   (`not_zeroTiltNearMinimizerReadoutUniform_abstract`).  Hence no abstract
   competitor/attainment axiom can close the residual; a geometric competitor at the
   actual lane (perturbing the frozen matching so that the frozen cost drops below
   `Iw 0 + δ` while the mark probe moves toward the limit readout) is required — the
   missing competitor-construction step of main.tex:9046-9050.  In particular the
   frozen attainment/matching-minimality (which identifies the OPTIMAL value) does not
   imply any near-minimizer probe modulus.
3. records that `ActualLaneReadoutSqueeze` and the V4 frozen-field derivative are then
   closed by the batch107/batch108 chain from the competitor form (no new input).

No `sorry`, `admit` or added axiom.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace Asymptotics
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

variable {A B : Set M}

/-- **The residual in competitor-comparison form**: if the mark probe of an admissible
matching exceeds the limit readout by more than δ, the frozen energy must exceed
`Iw 0 + δ` (so the matching is not almost kinetic-minimal). -/
def ProbeExcessForcesEnergyExcess {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ) : Prop :=
  ∀ (f : FinalProbeSpace A B) (δ : ℝ), 0 < δ → ∀ c ∈ (datum f).Cw,
    δ < |(datum f).P c - p f| → (datum f).K c > (datum f).Iw 0 + δ

/-- The uniform near-minimizer readout is exactly the competitor-comparison form. -/
theorem zeroTiltNearMinimizerReadoutUniform_iff_probeExcessForcesEnergyExcess
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ) :
    ZeroTiltNearMinimizerReadoutUniform datum p ↔
      ProbeExcessForcesEnergyExcess datum p := by
  constructor
  · intro h f δ hδ c hc hgt
    by_contra hle
    have hbound := h f δ hδ c hc (le_of_not_gt hle)
    linarith
  · intro h f δ hδ c hc hK
    by_contra hlt
    have hgt : δ < |(datum f).P c - p f| := not_le.mp hlt
    have := h f δ hδ c hc hgt
    linarith

/-- A legitimate abstract datum: `K = 0`, `P = 1`, weighted and second-moment classes
everything, a bounded competitor; the probe bound is `G = 1` and `Cb = 0`. -/
noncomputable def counterDatum : StationaryPressureDatum ℝ 1 0 where
  K := fun _ => 0
  P := fun _ => 1
  Cw := Set.univ
  C2 := Set.univ
  C2_subset_Cw := fun _ _ => trivial
  kinetic_nonneg := fun _ _ => le_refl 0
  probe_bound := fun _ _ => by norm_num
  competitor := 0
  competitor_mem := Set.mem_univ 0
  kinetic_competitor_le := by norm_num
  competitor2 := 0
  competitor2_mem := Set.mem_univ 0
  kinetic_competitor2_le := by norm_num

/-- The counter-datum's weighted pressure at tilt zero is zero. -/
theorem counterDatum_Iw_zero : counterDatum.Iw 0 = 0 := by
  show stationaryValue (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (1 : ℝ)) Set.univ 0 = 0
  unfold stationaryValue
  simp

/-- **Independence witness**: the uniform near-minimizer bound is not derivable from the
installed `StationaryPressureDatum` axioms — for a nonempty probe space there is a
legitimate datum family where it fails.  A genuine geometric competitor is therefore
required. -/
theorem not_zeroTiltNearMinimizerReadoutUniform_abstract
    (φ : FinalProbeSpace A B) :
    ¬ ZeroTiltNearMinimizerReadoutUniform
      (fun _ : FinalProbeSpace A B => counterDatum) (fun _ => 0) := by
  intro h
  have hK0 : counterDatum.K (0 : ℝ) = 0 := rfl
  have hK : counterDatum.K (0 : ℝ) ≤ counterDatum.Iw 0 + 1 / 2 := by
    rw [hK0, counterDatum_Iw_zero]
    norm_num
  have hP : |counterDatum.P (0 : ℝ) - (fun _ : FinalProbeSpace A B => (0 : ℝ)) φ| ≤ 1 / 2 :=
    h φ (1 / 2) (by norm_num) (0 : ℝ) (Set.mem_univ 0) hK
  have hval : counterDatum.P (0 : ℝ) = 1 := rfl
  rw [hval] at hP
  norm_num at hP

end OTSelector.Reconstruction
