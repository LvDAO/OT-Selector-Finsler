import OTSelector.Reconstruction.OriginalIIDRawPalmRootLabelLaw
import OTSelector.Reconstruction.OriginalIIDActualKineticClosure

/-!
# Actual clock-cutoff loss for the unchanged raw Palm candidate

The actual conditional matching profile supplies its original scaled clock
marginals and forwardness. The exact original root-label law then transports
the original population-a.e. cutoff estimate to the same raw root measure.
Zero-intensity roots are treated as zero measures; no positive density bound
or replacement matching candidate is introduced.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000

local instance actualClockCutoffPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace

/-- The true profile transfers its positive original clock gap to the same
raw paired-edge Palm, including all full transverse displacement marks. -/
theorem ae_original_raw_palm_forward_of_matching_profile
    (q : ℕ) (gap θ : ℝ) (hgap : 0 < gap)
    (α β : Measure ℝ)
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q) :
    ∀ᵐ m ∂cubePalm (Fin q) (physicalScenePairCampbell (Q.map Prod.fst)),
      m.1.1 < m.1.2 := by
  have hplan : ∀ᵐ s ∂Q,
      ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 < e.2.2 := by
    filter_upwards [h.2.2.2.2.2] with s hs
    filter_upwards [hs.2.2.2.1] with e he
    linarith
  have hbad : MeasurableSet {e : LegalMarkedPhysicalEdge q | ¬ e.1.2 < e.2.2} :=
    (measurableSet_lt measurable_fst.snd measurable_snd.snd).compl
  have hm : Measurable (fun scene : CavityLocalScene (LegalMarkedPhysicalPoint q)
      (LegalMarkedPhysicalPoint q) ↦
      (scene.1 : Measure (LegalMarkedPhysicalEdge q)) {e | ¬ e.1.2 < e.2.2}) :=
    (Measure.measurable_coe hbad).comp (measurable_localFiniteMeasure_coe.comp measurable_fst)
  have hS : MeasurableSet {scene : CavityLocalScene (LegalMarkedPhysicalPoint q)
      (LegalMarkedPhysicalPoint q) |
      ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 < e.2.2} := by
    simpa only [ae_iff] using measurableSet_eq_fun hm (measurable_const (a := (0 : ℝ≥0∞)))
  exact ae_cubePalm_physicalScene_forward _
    ((ae_map_iff measurable_fst.aemeasurable hS).mpr hplan)

/-- A cutoff valid for every actual forward coupling controls the unchanged
raw Palm with its original total mass. Marginals, mass, and forwardness are
proved from the actual matching profile, and theta zero is handled directly. -/
theorem original_raw_clock_cutoff_missed_le_of_matching_profile
    (q : ℕ) (gap θ : ℝ) (hgap : 0 < gap) (hθ : 0 ≤ θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q)
    (ψ : C(ℝ × ℝ,ℝ)) (clockLoss : ℝ≥0∞)
    (hcutoff : ∀ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π α β →
      (∀ᵐ c ∂π, c.1 ≤ c.2) → (∫⁻ c, ENNReal.ofReal (1-ψ c) ∂π) ≤ clockLoss) :
    let palm := cubePalm (Fin q) (physicalScenePairCampbell (Q.map Prod.fst))
    (∫⁻ m, ENNReal.ofReal (1-ψ m.1) ∂palm) ≤ palm univ * clockLoss := by
  intro palm
  let : IsProbabilityMeasure Q := h.1
  have hraw := original_raw_campbell_of_stationary_full_input_profile q θ hθ α β Q
    h.2.2.1 (h.2.2.2.2.2.mono fun s hs ↦ hs.2.1) h.2.2.2.1
  have hmass : palm univ = ENNReal.ofReal θ := hraw.2.2.1
  by_cases hzero : θ = 0
  · have hpalm : palm = 0 := Measure.measure_univ_eq_zero.mp (by simpa only [hzero, ENNReal.ofReal_zero] using hmass)
    simp only [hpalm, lintegral_zero_measure, Measure.coe_zero, Pi.zero_apply, zero_mul, le_refl]
  · have hpositive : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hforward : ∀ᵐ m ∂palm, m.1.1 ≤ m.1.2 :=
      (ae_original_raw_palm_forward_of_matching_profile q gap θ hgap α β input Q h).mono
        fun m hm ↦ hm.le
    rw [hmass]
    exact lintegral_raw_clock_cutoff_missed_le palm α β θ hpositive
      hraw.2.2.2.1 hraw.2.2.2.2 hforward ψ clockLoss hcutoff

section ActualPopulation
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

/-- A population-a.e. cutoff estimate for the original conditional clocks
controls the SAME actual raw Palm for its own unnormalized root law. Only
the genuine old-core matching profile is used; no Palm clock fields, clock
support, energy bound, or uniform positive intensity is assumed. -/
theorem PopulationHaarPressureCore.ae_fixed_candidate_raw_clock_cutoff_missed_le
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
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
    let α := fun c ↦ condDistrib u a η₀ (root c)
    let β := fun c ↦ condDistrib u a η₁ (root c)
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (gap : ℝ) (_hgap : 0 < gap)
      (input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
        LocalFiniteMeasure (LegalMarkedPhysicalPoint q))),
      (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
        OriginalIIDConditionalMatchingProfile gap
          (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
          (α c) (β c) (input c) (Λ c)) →
      ∀ (ψ : C(ℝ × ℝ,ℝ)) (_hrange : ∀ p, ψ p ∈ Icc 0 1) (clockLoss : ℝ≥0∞)
        {L : Set (ℚ → M)}, MeasurableSet L → L ⊆ C.roots →
        (∀ᵐ z ∂lambda.restrict L, ∀ π : Measure (ℝ × ℝ),
          Vlasov.IsCoupling π (condDistrib u a η₀ z) (condDistrib u a η₁ z) →
          (∀ᵐ p ∂π, p.1 ≤ p.2) →
          (∫⁻ p, ENNReal.ofReal (1-ψ p) ∂π) ≤ clockLoss) →
        ∀ᵐ c ∂(fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)).restrict
          (e '' (R '' L)),
          (∫⁻ m, ENNReal.ofReal (1-ψ m.1) ∂originalIIDRawPairPalmKernel Λ c) ≤
            originalIIDRawPairPalmKernel Λ c univ * clockLoss := by
  intro C S q e R K ref root α β Λ gap hgap input hprofile ψ _hrange clockLoss L hL hsub hcutoff
  let (c : Fin q → ℝ) : IsProbabilityMeasure (α c) := inferInstance
  let (c : Fin q → ℝ) : IsProbabilityMeasure (β c) := inferInstance
  have hrootLaw := D.fixed_candidate_raw_palm_root_label_law hF hcomplete hu ha hinj i
    Λ gap α β (fun c ↦ inferInstance) (fun c ↦ inferInstance) input hprofile hL hsub
  have hcutoffRaw := hrootLaw.2.2 _ hcutoff
  have hprofileA := ae_restrict_of_ae_restrict_of_subset (image_mono (image_mono hsub)) hprofile
  have hac : (fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)).restrict
      (e '' (R '' L)) ≪ (volume : Measure (Fin q → ℝ)).restrict (e '' (R '' L)) :=
    (withDensity_absolutelyContinuous volume
      (fun c ↦ originalIIDRawPairPalmKernel Λ c univ)).restrict _
  filter_upwards [hac.ae_le hprofileA, hcutoffRaw] with c hc hcutoffc
  have hθ : 0 ≤ originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c) :=
    mul_nonneg (NNReal.coe_nonneg _)
      (populationAtlasTheta_nonneg P a κ lambda C.seedIndex (ref c))
  simpa only [originalIIDRawPairPalmKernel_apply] using
    original_raw_clock_cutoff_missed_le_of_matching_profile q gap _ hgap hθ
      (α c) (β c) (input c) (Λ c) hc ψ clockLoss hcutoffc

end ActualPopulation
end OTSelector.Reconstruction
