import OTSelector.Reconstruction.FinslerOriginalClosedWindowClassPressure
import OTSelector.Reconstruction.FinslerOriginalClosedWindowRangePressure

/-! The literal physical reference class pressures converge to the canonical
measurable original retained-root pressure. All conditional and pressure laws
are produced from the unchanged original experiment. -/
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
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Actual finite physical class-model pressure limits converge to the exact
canonical measurable retained-root pressure. The range lift, full endpoint
bins and ALL thermodynamic limits are produced internally. The local gap
certificate is the one already exported by the actual geometric core factory. -/
theorem PopulationLocalPressureCore.ae_originalClosedWindow_physical_class_pressure_convergence
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
        ∀ t, Tendsto (fun n ↦ pref n t) atTop
          (𝓝 (originalSeedRetainedRootPressure (P C.seedIndex).seed a χ b f z t)) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let χ := D.originalClosedWindowPairKernel hcomplete γ
  have hsame := D.ae_originalClosedWindow_scalePressure_eq_range γ hF hcomplete hu ha hinj horder
    hb hμreg hνreg hμinv hνinv hlabel hgap.le hδ hδ1 f i
  filter_upwards [hsame,ae_restrict_of_ae hsep] with z hscale hzsep
  intro hz
  have hzpop : z ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,hz⟩
  have hgood := (D.haar.continuous.population.good z hzpop).1
  obtain ⟨π,⟨_hπ,hmap⟩,_⟩ := existsUnique_subtype_coupling_lift hrange.measurableSet hrange.measurableSet
    hgood.2.2.1 hgood.2.2.2 hgood.1
  have hq : 4 < finrank ℝ (P C.seedIndex).seed.covector.ker := by
    have hh := (P C.seedIndex).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at hh
    omega
  obtain ⟨law,hlaw,Q,hRdata,hfull,p,pref,hp,hpref,hconv⟩ :=
    D.exists_originalClosedWindow_class_pressure_convergence hrange γ hF hcomplete hu ha hinj
      i ⟨z,hz⟩ π hmap (hwindowGap ⟨z,hz⟩) hzsep hq hη hgap hδ hδ1 f
  have heq t : originalSeedRetainedRootPressure (P C.seedIndex).seed a χ b f z t = p t := by
    have hlim : Tendsto (fun R ↦ originalSeedRetainedScalePressure
        (P C.seedIndex).seed a χ b f R t z) atTop (𝓝 (p t)) :=
      (hp t).congr' (Filter.Eventually.of_forall fun R ↦ (hscale hz π hmap law hlaw R t).symm)
    exact hlim.limUnder_eq
  refine ⟨Q,hRdata,hfull,pref,hpref,?_⟩
  intro t
  rw [heq]
  exact hconv t

end OTSelector.Reconstruction
