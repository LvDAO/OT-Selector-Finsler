import OTSelector.Reconstruction.OriginalIIDFixedCandidateRootRecovery
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicOriginalCoefficient

/-!
# Exact original root law of the fixed raw Palm candidate

The actual matching profile identifies the unnormalized root mass on every
measured retained-root subset. The original seed label and its measurable
original root readout transport this same mass in both directions, so arbitrary
almost-everywhere properties pass from the original population to the raw Palm
root measure without a measurability assumption on the property.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000

section Readout
variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

/-- A measurable original root readout recovers exactly the original restricted
population measure from its actual coordinate pushforward. -/
theorem measurePreserving_readout_of_eq_map_on
    (lambda : Measure Z) (mu : Measure V) (label : Z → V) (ref : V → Z)
    (hlabel : Measurable label) (href : Measurable ref)
    {L : Set Z} (hL : MeasurableSet L)
    (hlaw : mu = (lambda.restrict L).map label)
    (hinv : ∀ z ∈ L, ref (label z) = z) :
    MeasurePreserving ref mu (lambda.restrict L) := by
  refine ⟨href, ?_⟩
  rw [hlaw, Measure.map_map href hlabel]
  have hcomp : (ref ∘ label) =ᵐ[lambda.restrict L] id := by
    filter_upwards [ae_restrict_mem hL] with z hz
    exact hinv z hz
  rw [Measure.map_congr hcomp, Measure.map_id]

/-- Exact readout transport transfers every a.e. predicate, including predicates
whose truth sets have not been shown measurable. -/
theorem ae_readout_of_measurePreserving
    (lambda : Measure Z) (mu : Measure V) (ref : V → Z)
    (hpres : MeasurePreserving ref mu lambda) {Q : Z → Prop}
    (hQ : ∀ᵐ z ∂lambda, Q z) : ∀ᵐ c ∂mu, Q (ref c) := by
  apply ae_of_ae_map hpres.measurable.aemeasurable
  rwa [hpres.map_eq]

end Readout

section ActualOriginalRootLaw
open Manifold OTSelector.Geometry
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The SAME actual raw Palm candidate has exactly the original population
root law on every measurable retained-root subset. Its measurable original
root readout preserves that law and transfers arbitrary population-a.e.
properties. Neither the law nor any energy bound is assumed. -/
theorem PopulationHaarPressureCore.fixed_candidate_raw_palm_root_label_law
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := Module.finrank ℝ S.covector.ker
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (gap : ℝ) (α β : (Fin q → ℝ) → Measure ℝ)
      (_ : ∀ c, IsProbabilityMeasure (α c)) (_ : ∀ c, IsProbabilityMeasure (β c))
      (input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
        LocalFiniteMeasure (LegalMarkedPhysicalPoint q))),
      (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
        OriginalIIDConditionalMatchingProfile gap
          (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
          (α c) (β c) (input c) (Λ c)) →
      ∀ {L : Set (ℚ → M)}, MeasurableSet L → L ⊆ C.roots →
        let raw := (fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)).restrict
          (e '' (R '' L))
        let label := fun z ↦ e (R z)
        let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
        raw = (lambda.restrict L).map label ∧
          MeasurePreserving root raw (lambda.restrict L) ∧
          ∀ (Q : (ℚ → M) → Prop), (∀ᵐ z ∂lambda.restrict L, Q z) →
            ∀ᵐ c ∂raw, Q (root c) := by
  intro C S q e R K ref Λ gap α β hα hβ input hprofile L hL hsub raw label root
  let _rootLawMetric : MetricSpace M := F.metricSpace
  let _rootLawProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _rootLawPolish : PolishSpace M := inferInstance
  let _rootLawBorel : BorelSpace (ℚ → M) := inferInstance
  have hlabel : Measurable label := e.continuous.measurable.comp
    (measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj)
  have hlaw : raw = (lambda.restrict L).map label := by
    ext A hA
    let L' := label ⁻¹' A ∩ L
    have hL' : MeasurableSet L' := (hA.preimage hlabel).inter hL
    have hsub' : L' ⊆ C.roots := fun z hz ↦ hsub hz.2
    have himage : e '' (R '' L') = A ∩ (e '' (R '' L)) := by
      simpa only [L', label, image_image] using image_preimage_inter label L A
    have hmass := D.fixed_candidate_raw_palm_mass_eq_label hF hcomplete hu ha hinj i
      Λ gap α β hα hβ input hprofile hL' hsub'
    change fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)
      (e '' (R '' L')) = lambda L' at hmass
    rw [show raw = (fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)).restrict
      (e '' (R '' L)) from rfl,
      Measure.restrict_apply hA, Measure.map_apply hlabel hA,
      Measure.restrict_apply (hA.preimage hlabel)]
    rw [← himage]
    exact hmass
  have hroot : Measurable root := measurable_physicalSceneOriginalMacroRootValue ha C.seedIndex
  have hinverse : ∀ z ∈ L, root (label z) = z := by
    intro z hz
    exact physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj C.seedIndex
      (C.roots_subset_piece (hsub hz))
  have hpres : MeasurePreserving root raw (lambda.restrict L) :=
    measurePreserving_readout_of_eq_map_on lambda raw label root hlabel hroot hL hlaw hinverse
  exact ⟨hlaw, hpres, fun Q hQ ↦
    ae_readout_of_measurePreserving (lambda.restrict L) raw root hpres hQ⟩

end ActualOriginalRootLaw
end OTSelector.Reconstruction
