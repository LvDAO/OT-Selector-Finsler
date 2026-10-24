import OTSelector.Reconstruction.OriginalIIDPressureLeadingIntegral
import OTSelector.Reconstruction.FinslerOriginalPhysicalUnitDensitySupportedUpper
import OTSelector.Reconstruction.FinslerSelectorFinalInputsWiringAudit

/-!
# Original same-atlas expected upper in the final selector interface

The final field `FinalProbUpperData` asks for an expected upper bound. The actual
original iid assignment upper therefore transfers by the existing exact iid-law
identity. One norm-preserving ambient extension is chosen for each compact probe,
while the potential, original atlas, measures, and root pressure stay fixed.

Zero-tilt integrability remains an explicit low-level analytic input. This module
does not add it to the final selector hypotheses or assert the remaining lower
bound, value identification, or derivative.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂ u₃
namespace OTSelector.Reconstruction
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- One ambient continuous extension for each final compact-carrier probe. -/
def originalFinalProbeAmbient (F : ContinuousFinslerNorm E M)
    (μ ν : ProbabilityMeasure M) {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    (f : FinalProbeSpace A B) : M × M →ᵇ ℝ := by
  let _inst : MetricSpace M := F.metricSpace
  exact Classical.choose (exists_original_supported_probe_ambient_extension μ ν (A ∪ B)
    (hA.union hB) (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy) f)

/-- The chosen extension preserves the exact norm and compact-carrier readout. -/
theorem originalFinalProbeAmbient_spec
    (μ ν : ProbabilityMeasure M) {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    (f : FinalProbeSpace A B) :
    ‖originalFinalProbeAmbient F μ ν hA hB hμA hνB f‖ = ‖f‖ ∧
    ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, originalFinalProbeAmbient F μ ν hA hB hμA hνB f (x,y) =
      f (supportProjection μ (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) x,
        supportProjection ν (A ∪ B) (hA.union hB).measurableSet
          (hνB.mono fun _ hy ↦ Or.inr hy) y) := by
  let _inst : MetricSpace M := F.metricSpace
  have h := Classical.choose_spec (exists_original_supported_probe_ambient_extension μ ν
    (A ∪ B) (hA.union hB) (hμA.mono fun _ hx ↦ Or.inl hx)
    (hνB.mono fun _ hy ↦ Or.inr hy) f)
  exact ⟨h.1,h.2.1⟩

variable {u : M → ℝ} {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {μ ν : ProbabilityMeasure M} {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
  {b : (ℚ → M) × ℝ → M} {r : ℝ}

/-- The final upper field is the actual original physical pressure integral in
one fixed chosen potential atlas, applied to the chosen ambient probe. -/
def originalSameAtlasUpperPressure
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → (ℚ → M))
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (μ ν : ProbabilityMeasure M) (b : (ℚ → M) × ℝ → M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B) :
    FinalPressureField A B :=
  fun f t ↦ ∫ z, originalPhysicalFinslerRootPressure P a κ ((μ : Measure M).map a)
    μ ν b (originalFinalProbeAmbient F μ ν hA hB hμA hνB f) t z ∂(μ : Measure M).map a

/-- The actual original full-iid upper supplies the final selector's upper field
for arbitrary iid realizations and any chosen tilt radius. All actual core, atlas,
and potential data are unchanged. Zero-tilt integrability is the existing low-level
analytic dependency; no final pressure inequality is assumed. -/
theorem original_same_atlas_final_hupper
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
    (hlaw : PopulationSeedPieceMomentLaw P a κ ((μ : Measure M).map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂(μ : Measure M), x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂(ν : Measure M), y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂(μ : Measure M), b (a x,u x) = x)
    (hνinv : ∀ᵐ y ∂(ν : Measure M), b (a y,u y) = y)
    (hlabel : (ν : Measure M).map a = (μ : Measure M).map a)
    (hdim : 6 ≤ finrank ℝ E) (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a ((μ : Measure M).map a) μ ν gap diameter)
    (hγ : ∀ᵐ z ∂(μ : Measure M).map a, Vlasov.IsCoupling (γ z)
      (condDistrib u a μ z) (condDistrib u a ν z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
    (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      r (δn n) (lossn n))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0))
    (hη : ∀ n, 0 < η n ∧ η n < 1)
    (hscreen : ∀ n i, (((D n).haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    (hp0 : ∀ f : FinalProbeSpace A B,
      Integrable (originalPhysicalFinslerRootPressure P a κ ((μ : Measure M).map a) μ ν b
        (originalFinalProbeAmbient F μ ν hA hB hμA hνB f) 0) ((μ : Measure M).map a))
    (hphysicalSep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    {Ω : ℕ → Type u₃} [∀ n, MeasurableSpace (Ω n)]
    (R : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (R n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (R n)) (hYi : ∀ n, iIndepFun (Y n) (R n))
    (hXlaw : ∀ n i, (R n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n j, (R n).map (Y n j) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun ξ i ↦ X n i ξ) (fun ξ j ↦ Y n j ξ) (R n))
    (radius : FinalRadiusField A B) :
    ∀ (f : FinalProbeSpace A B) (t ε : ℝ), |t| < radius f → 0 < ε →
      ∀ᶠ n in atTop,
        ∫ sample, finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i sample) (fun j ↦ Y n j sample) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((finrank ℝ E : ℝ) - 1))) f t ∂R n ≤
          originalSameAtlasUpperPressure P a κ μ ν b hA hB hμA hνB f t + ε := by
  intro f t ε _ht hε
  let g := originalFinalProbeAmbient F μ ν hA hB hμA hνB f
  have hg := (originalFinalProbeAmbient_spec (F := F) μ ν hA hB hμA hνB f).2
  have hupper := original_full_iid_pressure_le_global_integral hrange γ hlaw hF hcomplete
    hu ha hinj horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep hγ
    δn lossn D hδ hδ1 hδlim hloss η hηlim hη hscreen g (hp0 f) hA hB hAB hμA hνB
    hphysicalSep πOriginal hπOriginal hcalOriginal t
  have hup := (tendsto_add_atTop_nat 1).eventually (hupper.2 ε hε)
  have hqdim : ((finrank ℝ E - 1 : ℕ) : ℝ) = (finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ finrank ℝ E), Nat.cast_one]
  filter_upwards [hup] with n hn
  rw [← hqdim]
  have htransfer := integral_finslerSupportedPressure_eq_original_assignment hcomplete μ ν (A ∪ B)
    (hA.union hB) (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
    (R n) (X n) (Y n) (hX n) (hY n) (hXi n) (hYi n) (hXlaw n) (hYlaw n) (hXY n)
    u hu f g hg t
  simp only [finslerMeanScale] at htransfer
  rw [htransfer]
  simpa only [finslerMeanScale, canonicalLaw, twoColourLaw, originalSameAtlasUpperPressure]
    using hn

end OTSelector.Reconstruction
