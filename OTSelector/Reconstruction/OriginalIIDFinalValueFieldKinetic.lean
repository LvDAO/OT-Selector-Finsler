import OTSelector.Reconstruction.OriginalFocalWindowPressureUpper
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCut

/-! The same actual original candidate can be read with its true focal kinetic cost. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Replacing a kinetic readout by an almost-everywhere equal one preserves the literal
original scene law, all original inputs and legal matching, and kinetic integrability. -/
def LegalWeightedStationaryPoissonMatching.withAEEqKinetic
    {q : ℕ} {α β : Measure ℝ} {kin kin' : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (heq : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, kin' m.1.1 m.1.2 m.2 = kin m.1.1 m.1.2 m.2) :
    LegalWeightedStationaryPoissonMatching q α β kin' g where
  law := Q.law
  stationary := Q.stationary
  full_matching := Q.full_matching
  forward := Q.forward
  input_laplace := Q.input_laplace
  palm_probability := Q.palm_probability
  source_clock := Q.source_clock
  target_clock := Q.target_clock
  kinetic_integrable := Q.kinetic_integrable.congr (heq.mono (fun _ h ↦ h.symm))
  probe_integrable := Q.probe_integrable

/-- The signed value of the unchanged actual original law is exactly preserved. -/
theorem LegalWeightedStationaryPoissonMatching.withAEEqKinetic_value
    {q : ℕ} {α β : Measure ℝ} {kin kin' : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (heq : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, kin' m.1.1 m.1.2 m.2 = kin m.1.1 m.1.2 m.2)
    (t : ℝ) : (Q.withAEEqKinetic heq).value t = Q.value t := by
  change (∫ m, kin' m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q Q.law) + _ = _
  rw [integral_congr_ae heq]
  rfl

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The original conditional support and strict forward clocks identify the actual full
matrix candidate with a focal candidate of precisely the same law and every signed value.
No displacement moment, minimizer selection or pressure comparison is used. -/
theorem OriginalSeedConditionalMoments.exists_sameLaw_originalFocalMatching_of_actual_matrix
    (D : OriginalSeedConditionalMoments S w μ ν)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (fun a b v ↦ matrixQuadratic (originalSeedPairCoefficient S w (a,b)) v) g) :
    ∃ Qf : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
      Qf.law = Q.law ∧ ∀ t, Qf.value t = Q.value t := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have hs : ∀ᵐ m ∂η, m.1.1-(S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support := by
    apply ae_of_ae_map (μ := η) (f := fun m ↦ m.1.1)
      (p := fun a : ℝ ↦ a-(S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support)
      measurable_fst.fst.aemeasurable
    rw [Q.source_clock]
    exact D.support.source.ae_open.and μ.support_mem_ae
  have ht : ∀ᵐ m ∂η, m.1.2-(S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support := by
    apply ae_of_ae_map (μ := η) (f := fun m ↦ m.1.2)
      (p := fun b : ℝ ↦ b-(S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support)
      measurable_fst.snd.aemeasurable
    rw [Q.target_clock]
    exact D.support.target.ae_open.and ν.support_mem_ae
  have heq : ∀ᵐ m ∂η, D.originalFocalKinetic gap m.1.1 m.1.2 m.2 =
      matrixQuadratic (originalSeedPairCoefficient S w m.1) m.2 := by
    filter_upwards [hs, ht, Q.ae_palm_forward] with m ha hb hf
    exact D.originalFocalKinetic_eq_of_original_support hbounds ha hb hf m.2
  exact ⟨Q.withAEEqKinetic heq, rfl, fun t ↦ Q.withAEEqKinetic_value heq t⟩

end OTSelector.Reconstruction
