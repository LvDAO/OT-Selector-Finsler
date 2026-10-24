import OTSelector.Reconstruction.FinslerOriginalClosedWindowPhysicalClassConvergence
import OTSelector.Reconstruction.FinslerOriginalClosedWindowPhysicalIntensity
import OTSelector.Reconstruction.FinslerOriginalRetainedGlobalPressure

/-! Literal physical class limits retain their exact Haar density power,
original-population inverse intensity, and actual rescaled physical tilt. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual physical P0 class pressures, with their SAME retained coordinate
intensity and true tilt, converge to the corrected global retained pressure
against the ORIGINAL root measure. The Haar factor is never set to one. -/
theorem PopulationLocalPressureCore.ae_originalClosedWindow_weighted_class_pressure_convergence
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
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
    (hdim : 6 ≤ finrank ℝ E) (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (i : Fin D.haar.continuous.count)
    (hwindowGap : (D.haar.continuous.coefficient i).roots.Nonempty →
      ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap) :
    let C := D.haar.continuous.coefficient i
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let χ := D.originalClosedWindowPairKernel hcomplete γ
    ∀ᵐ z ∂(μ.map a).restrict C.roots, ∀ hz : z ∈ C.roots,
      ∃ Q : ∀ n : ℕ, FiniteScalarBins range (1 / ((n:ℝ)+2)),
        (∀ n, Nonempty (OriginalRangeClockResamplingData C (Q n) z hz f
          (1 / ((n:ℝ)+2)) (1 / ((n:ℝ)+2)))) ∧
        (∀ n j k, C.clockClassAllowed (Q n) j k → ∀ x ∈ (Q n).cell j, ∀ y ∈ (Q n).cell k,
          x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) ∧
      ∃ pref : ℕ → ℝ → ℝ,
        (∀ n t, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ⟨z,hz⟩ (Q n)
          hη hgap.le hδ hδ1 f R t) atTop (𝓝 (pref n t))) ∧
        let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex z
        let density := fun n ↦
          (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
          (clockClassPairMeasure
            (D.originalWindowReferenceWeights γ gap range i ⟨z,hz⟩ (Q n) η)).real univ
        ∀ t, Tendsto (fun n ↦ theta⁻¹ * (density n) ^ (1-2/(q:ℝ)) *
          pref n (t * (density n) ^ (2/(q:ℝ)))) atTop
          (𝓝 (originalRetainedFinslerRootPressure P a κ (μ.map a)
            (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 t z)) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := finrank ℝ (P C.seedIndex).seed.covector.ker
  let χ := D.originalClosedWindowPairKernel hcomplete γ
  have hactual := D.ae_originalClosedWindow_physical_class_pressure_convergence hrange γ hF hcomplete
    hu ha hinj horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep hδ hδ1 hη f i hwindowGap
  filter_upwards [hactual] with z hclass
  intro hz
  obtain ⟨Q,hRdata,hfull,pref,hpref,hconv⟩ := hclass hz
  refine ⟨Q,hRdata,hfull,pref,hpref,?_⟩
  dsimp only
  let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex z
  let d := ((1-η) * theta) * (χ z).real univ
  let density := fun n ↦
    (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
      (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap range i ⟨z,hz⟩ (Q n) η)).real univ
  have hd n : density n = d := by
    exact D.originalWindowReferenceWeights_coordinate_intensity hrange.measurableSet γ hcomplete i ⟨z,hz⟩
      (Q n) (hwindowGap ⟨z,hz⟩) (hfull n) hη hgap.le hδ hδ1
  intro t
  have htarget : originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 t z =
      theta⁻¹ * d ^ (1-2/(q:ℝ)) *
        originalSeedRetainedRootPressure (P C.seedIndex).seed a χ b f z (t*d^(2/(q:ℝ))) := by
    rw [originalRetainedFinslerRootPressure_eq_on_piece P a κ (μ.map a)
      (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 C.seedIndex t (C.roots_subset_piece hz)]
    rfl
  rw [htarget]
  have hlim := (hconv (t*d^(2/(q:ℝ)))).const_mul (theta⁻¹*d^(1-2/(q:ℝ)))
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    change theta⁻¹*d^(1-2/(q:ℝ))*pref n (t*d^(2/(q:ℝ))) =
      theta⁻¹*(density n)^(1-2/(q:ℝ))*pref n (t*(density n)^(2/(q:ℝ)))
    rw [hd n]

end OTSelector.Reconstruction
