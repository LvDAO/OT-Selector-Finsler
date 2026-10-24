import OTSelector.Reconstruction.FinslerOriginalClosedWindowWeightedClassConvergence
import OTSelector.Reconstruction.OriginalClockResamplingAccuracy

/-! One actual finite physical class model simultaneously meets the requested
coefficient/probe tolerances and its corrected original-root pressure bound. -/
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

/-- Actual original data select ONE finite bin model at the requested geometry,
physical-probe, and corrected pressure tolerances. Its width contract is the
original positive support gap, exactly as the physical iid factory requires.
The same bins carry all three certificates before any samples are drawn. -/
theorem PopulationLocalPressureCore.ae_exists_original_physical_class_model
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
      ∀ t ε probeError tolerance : ℝ, 0 < ε → 0 < probeError → 0 < tolerance →
      ∃ Q : FiniteScalarBins range gap,
        Nonempty (OriginalRangeClockResamplingData C Q z hz f ε probeError) ∧
        (∀ j k, C.clockClassAllowed Q j k → ∀ x ∈ Q.cell j, ∀ y ∈ Q.cell k,
          x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) ∧
      ∃ pref : ℝ → ℝ,
        (∀ τ, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ⟨z,hz⟩ Q
          hη hgap.le hδ hδ1 f R τ) atTop (𝓝 (pref τ))) ∧
        let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex z
        let density := (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
          (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap range i ⟨z,hz⟩ Q η)).real univ
        theta⁻¹ * density^(1-2/(q:ℝ)) * pref (t*density^(2/(q:ℝ))) <
          originalRetainedFinslerRootPressure P a κ (μ.map a)
            (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 t z + tolerance := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := finrank ℝ (P C.seedIndex).seed.covector.ker
  let χ := D.originalClosedWindowPairKernel hcomplete γ
  have hactual := D.ae_originalClosedWindow_weighted_class_pressure_convergence hrange γ hF hcomplete
    hu ha hinj horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep hδ hδ1 hη f i hwindowGap
  filter_upwards [hactual] with z hclass
  intro hz t ε probeError tolerance hε hprobe htolerance
  obtain ⟨Qn,hRdata,hfull,pref,hpref,hconv⟩ := hclass hz
  have hacc : Tendsto (fun n : ℕ ↦ 1/((n:ℝ)+2)) atTop (𝓝 0) := by
    have hh := tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop)
    simpa only [one_div,Function.comp_def] using hh
  have hsmall : ∀ᶠ (n : ℕ) in atTop, 1/((n:ℝ)+2) < gap ∧
      1/((n:ℝ)+2) ≤ ε ∧ 1/((n:ℝ)+2) ≤ probeError := by
    filter_upwards [hacc.eventually (gt_mem_nhds hgap),hacc.eventually (gt_mem_nhds hε),
      hacc.eventually (gt_mem_nhds hprobe)] with n hg he hp
    exact ⟨hg,he.le,hp.le⟩
  have hpressure := (hconv t).eventually
    (gt_mem_nhds (lt_add_of_pos_right _ htolerance))
  obtain ⟨n,hn,hpn⟩ := (hsmall.and hpressure).exists
  let Q := (Qn n).relaxWidth hn.1.le
  let Rdata := (hRdata n).some
  refine ⟨Q,⟨(Rdata.increaseErrors hn.2.1 hn.2.2).relaxWidth hn.1.le⟩,hfull n,pref n,?_,?_⟩
  · intro τ
    have heq R : D.originalWindowClassScalePressure γ gap i ⟨z,hz⟩ Q
        hη hgap.le hδ hδ1 f R τ =
        D.originalWindowClassScalePressure γ gap i ⟨z,hz⟩ (Qn n)
          hη hgap.le hδ hδ1 f R τ := rfl
    exact (hpref n τ).congr' (Filter.Eventually.of_forall fun R ↦ (heq R).symm)
  · exact hpn

end OTSelector.Reconstruction
