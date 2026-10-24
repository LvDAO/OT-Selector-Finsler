import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowMeasureLaw

/-!
# Exact original input window laws on the actual vague carrier

The finite-plan local version lifts the already identified literal finite
Poisson window measure law to the same locally finite carrier used by the
joint scene. Every compact-window restriction is finite internally, so this
lift is pointwise the original measure, with no exceptional replacement.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

section Restriction
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]

/-- Literal restriction of the same actual input on its vague carrier. -/
def legalInputRestrictionLocal (U : Set X) (μ : LocalFiniteMeasure X) : LocalFiniteMeasure X :=
  ⟨(μ : Measure X).restrict U, inferInstance⟩

theorem measurable_legalInputRestrictionLocal {U : Set X} (hU : MeasurableSet U) :
    Measurable (legalInputRestrictionLocal (X := X) U) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  apply Measure.measurable_of_measurable_coe
  intro V hV
  simpa only [legalInputRestrictionLocal, Measure.restrict_apply hV, Function.comp_def] using
    (Measure.measurable_coe (hV.inter hU)).comp measurable_localFiniteMeasure_coe

/-- Compactness makes the local-version fallback unused for every actual
input, rather than only on an assumed full-probability event. -/
theorem finitePlanLocalVersion_restrict_compact_eq {U : Set X} (hU : IsCompact U)
    (μ : LocalFiniteMeasure X) :
    finitePlanLocalVersion (id : Measure X → Measure X) ((μ : Measure X).restrict U) =
      legalInputRestrictionLocal U μ := by
  apply Subtype.ext
  rw [coe_finitePlanLocalVersion]
  have hfinite : ((μ : Measure X).restrict U) univ < ⊤ := by
    simpa only [Measure.restrict_apply_univ] using hU.measure_lt_top (μ := (μ : Measure X))
  exact ite_eq_left hfinite
end Restriction

local instance markedStationaryValueLegalInputWindowLocalLawInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputWindowLocalLawPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The same actual weak input on any compact marked window has the entire
original independent Poisson-prefix law on the locally finite carrier. -/
theorem map_legalMarkedInput_restrictionLocal_eq_originalPoisson_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0,
      (Q : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ legalInputRestrictionLocal U s.2) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ legalInputRestrictionLocal U (legalInputTwoBlockLocal q b)) := by
  obtain ⟨S, hS, hraw⟩ := map_legalMarkedInput_restrict_eq_originalPoisson_of_tendsto
    q α β kin hk g hg t L hL hlarge hweak hU
  let F := finitePlanLocalVersion (id : Measure (LegalColoredInputPoint q) → Measure (LegalColoredInputPoint q))
  have hF : Measurable F := measurable_finitePlanLocalVersion id measurable_id
  have hrestrict : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) :=
    measurable_localFiniteMeasure_coe.comp (measurable_legalInputRestrictionLocal hU.measurableSet)
  have h1 : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)).restrict U) := hrestrict.comp measurable_snd
  have h2 : Measurable (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) := by
    exact hrestrict.comp (measurable_legalInputTwoBlockLocal q)
  have h := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦ P.map F) hraw
  rw [Measure.map_map hF h1, Measure.map_map hF h2] at h
  have hb (b) : F ((legalInputTwoBlockMeasure q b).restrict U) =
      legalInputRestrictionLocal U (legalInputTwoBlockLocal q b) :=
    finitePlanLocalVersion_restrict_compact_eq hU (legalInputTwoBlockLocal q b)
  refine ⟨S, hS, ?_⟩
  simpa only [Function.comp_def, hb, F, finitePlanLocalVersion_restrict_compact_eq hU] using h

end OTSelector.Reconstruction
