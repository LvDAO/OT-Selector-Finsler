import OTSelector.Reconstruction.FinslerOriginalClosedWindowPairKernel
import OTSelector.Reconstruction.FinslerOriginalRetainedRootPressure
import OTSelector.Reconstruction.FinslerOriginalCanonicalClockPressure
import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery

/-! The canonical measurable physical retained pressure is exactly the
original coefficient-core pressure with its actual complete-curve probe.
The two descriptions use the same original normalized conditional marginals. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The true original scalar-legal pressure at every real scale depends only
on the actual original costs on its legal product law. -/
theorem legalMarkedScalePressure_congr_of_ae_on_legal
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin kin' : A → B → (Fin q → ℝ) → ℝ) (probe probe' : A → B → ℝ)
    (hcost : ∀ᵐ p ∂α.prod β, source p.1 < target p.2 →
      (∀ v, kin p.1 p.2 v = kin' p.1 p.2 v) ∧ probe p.1 p.2 = probe' p.1 p.2)
    (R t : ℝ) :
    legalMarkedScalePressure q source target α β kin probe R t =
      legalMarkedScalePressure q source target α β kin' probe' R t := by
  by_cases hR : 0 < R
  · simp only [legalMarkedScalePressure,hR,ite_true]
    rw [legalMarkedPressure_congr_of_ae_on_legal q source target α β kin kin' probe probe' hcost]
  · simp only [legalMarkedScalePressure,hR,ite_false]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Original almost-everywhere physical recovery identifies the measurable
retained pressure with the actual coefficient matrix and complete-curve probe
at every real scale. This is equality of the same original experiment. -/
theorem PopulationLocalPressureCore.ae_originalClosedWindow_scalePressure_eq_core
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hlabel : ν.map a = μ.map a)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (f : M × M →ᵇ ℝ) (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let χ := D.originalClosedWindowPairKernel hcomplete γ
    ∀ᵐ z ∂(μ.map a).restrict C.roots, ∀ hz : z ∈ C.roots, ∀ R t,
      originalSeedRetainedScalePressure (P C.seedIndex).seed a χ b f R t z =
        legalMarkedScalePressure (finrank ℝ (P C.seedIndex).seed.covector.ker) id id
          ((originalNormalizedRetainedPairKernel χ).map Prod.fst z)
          ((originalNormalizedRetainedPairKernel χ).map Prod.snd z)
          (fun x y w ↦ matrixQuadratic (C.matrix z (x,y)) w)
          (fun x y ↦ originalReferenceClockProbe C z hz f (x,y)) R t := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let χ := D.originalClosedWindowPairKernel hcomplete γ
  let S := (P C.seedIndex).seed
  let label := populationSeedRootLabelValue S a
  have hcurve := D.haar.original_inverse_ae_of_ae_recovery hF hcomplete hu ha hinj horder hb
    hμreg hνreg hμinv hνinv rfl hlabel i
  filter_upwards [hcurve] with z he
  intro hz R t
  have hzpop : z ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,hz⟩
  have hgood := (D.haar.continuous.population.good z hzpop).1
  have hχ : χ z = (γ z).restrict C.window.region :=
    D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i z hz
  have hmass : 0 < (χ z).real univ :=
    (sub_pos.mpr hδ1).trans
      (D.originalClosedWindowPairKernel_mass_lower γ hcomplete hgap hδ i ⟨z,hz⟩)
  let law := normalizedFiniteLaw ((γ z).restrict C.window.region)
  have hlawpos : 0 < ((γ z).restrict C.window.region).real univ := by rwa [hχ] at hmass
  letI : IsProbabilityMeasure law := normalizedFiniteLaw_probability _ hlawpos
  have hα : (originalNormalizedRetainedPairKernel χ).map Prod.fst z = law.map Prod.fst := by
    rw [Kernel.map_apply _ measurable_fst,originalNormalizedRetainedPairKernel_apply_eq χ z hmass,hχ]
  have hβ : (originalNormalizedRetainedPairKernel χ).map Prod.snd z = law.map Prod.snd := by
    rw [Kernel.map_apply _ measurable_snd,originalNormalizedRetainedPairKernel_apply_eq χ z hmass,hχ]
  have hsub : (γ z).restrict C.window.region ≤ γ z := Measure.restrict_le_self
  have hac : law ≪ γ z := (Measure.absolutelyContinuous_of_le hsub).smul_left _
  have hαac : law.map Prod.fst ≪ condDistrib u a μ z := by
    rw [← hgood.1.1]
    exact hac.map measurable_fst
  have hβac : law.map Prod.snd ≪ condDistrib u a ν z := by
    rw [← hgood.1.2]
    exact hac.map measurable_snd
  have hprobe x y : originalReferenceClockProbe C z hz f (x,y) =
      f (S.curve (label z) (x-S.level),S.curve (label z) (y-S.level)) := by
    dsimp only [originalReferenceClockProbe,label,S]
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
      ⟨z,C.roots_subset_piece hz⟩]
  have hs : ∀ᵐ x ∂(originalNormalizedRetainedPairKernel χ).map Prod.fst z,
      b (z,x) = S.curve (label z) (x-S.level) := by
    rw [hα]
    exact hαac.ae_le he.1
  have ht : ∀ᵐ y ∂(originalNormalizedRetainedPairKernel χ).map Prod.snd z,
      b (z,y) = S.curve (label z) (y-S.level) := by
    rw [hβ]
    exact hβac.ae_le he.2
  unfold originalSeedRetainedScalePressure
  apply legalMarkedScalePressure_congr_of_ae_on_legal
  filter_upwards [ae_fst_of_ae hs,ae_snd_of_ae ht] with p hp₀ hp₁
  intro _
  refine ⟨fun _ ↦ rfl,?_⟩
  rw [hprobe]
  change f (b (z,p.1),b (z,p.2)) = _
  rw [hp₀,hp₁]

end OTSelector.Reconstruction
