import OTSelector.Reconstruction.OriginalIIDRefinedPressureReadout
import OTSelector.Reconstruction.FinslerOriginalPhysicalPressureContinuityCore

/-!
# Pressure screens before original finite reference selection

Compact restrictions preserve the actual original coefficient windows and conditional
closed-window law. A pressure cutoff and a Lusin continuity core are selected before
finite references; all later reference roots therefore satisfy the same retained
properties. The root measure is neither renormalized nor replaced.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- A compact Lusin restriction preserves a signed pressure integral up to an
arbitrarily small error. The same compact set carries an arbitrary original AE
property. A common lower bound controls the integral over the removed roots. -/
theorem exists_compact_pressure_reference_screen
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (lambda : Measure X) [IsFiniteMeasure lambda] {H : Set X} (hH : MeasurableSet H)
    {p q : X → ℝ} (hp : IntegrableOn p H lambda) (hq : AEStronglyMeasurable q lambda)
    {Good : X → Prop} (hGood : ∀ᵐ z ∂lambda.restrict H, Good z)
    {B : ℝ} (hB : 0 ≤ B) (hlower : ∀ᵐ z ∂lambda.restrict H, -B ≤ p z)
    {budget tolerance : ℝ} (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    ∃ K ⊆ H, IsCompact K ∧ lambda.real (H \ K) < budget ∧
      ContinuousOn p K ∧ ContinuousOn q K ∧
      (∀ z ∈ K, Good z) ∧ IntegrableOn p K lambda ∧
      (∫ z in K, p z ∂lambda) < (∫ z in H, p z ∂lambda) + tolerance := by
  obtain ⟨τ, hτ, hBτ⟩ := exists_pos_mul_lt htolerance B
  let η := min budget τ
  have hη : 0 < η := lt_min hbudget hτ
  let pB := hp.aestronglyMeasurable.mk p
  let qB := hq.mk q
  have hpB : Measurable pB := hp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hqB : Measurable qB := hq.stronglyMeasurable_mk.measurable
  have hprop : ∀ᵐ z ∂lambda.restrict H, pB z = p z ∧ qB z = q z ∧ Good z :=
    hp.aestronglyMeasurable.ae_eq_mk.symm.and
      ((ae_restrict_of_ae hq.ae_eq_mk.symm).and hGood)
  obtain ⟨K, hKH, hK, hsmall, hcont, hall⟩ :=
    exists_lusin_compact_core_with_ae_property hH (measure_ne_top lambda H)
      (hpB.prodMk hqB) hprop (ENNReal.ofReal_pos.mpr hη).ne'
  have hmass : lambda.real (H \ K) < η := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal hη.le] using
      (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hsmall
  have hpK : IntegrableOn p K lambda := hp.mono_set hKH
  have hpD : IntegrableOn p (H \ K) lambda := hp.mono_set sdiff_subset
  have hlowerD : ∀ᵐ z ∂lambda.restrict (H \ K), -B ≤ p z :=
    ae_restrict_of_ae_restrict_of_subset sdiff_subset hlower
  have hlow : -(B * lambda.real (H \ K)) ≤ ∫ z in H \ K, p z ∂lambda := by
    have hh := integral_mono_ae (integrable_const (-B)) hpD hlowerD
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_neg,
      neg_mul, mul_comm] using hh
  have hsplit : (∫ z in K, p z ∂lambda) + (∫ z in H \ K, p z ∂lambda) =
      ∫ z in H, p z ∂lambda := by
    have hh := integral_inter_add_sdiff hK.measurableSet hp
    simpa only [inter_eq_right.mpr hKH] using hh
  refine ⟨K, hKH, hK, hmass.trans_le (min_le_left _ _),
    hcont.fst.congr (fun z hz ↦ (hall z hz).1.symm),
    hcont.snd.congr (fun z hz ↦ (hall z hz).2.1.symm),
    fun z hz ↦ (hall z hz).2.2, hpK, ?_⟩
  have herror : B * lambda.real (H \ K) < tolerance :=
    (mul_le_mul_of_nonneg_left (hmass.le.trans (min_le_right _ _)) hB).trans_lt hBτ
  linarith

variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss loss' : ℝ≥0∞} {Good : (ℚ → M) → Prop}

/-- Restrict an actual local core to compact subsets of its coefficient pieces.
All original seed, window, intensity, inverse-moment and distance data are retained. -/
def PopulationLocalPressureCore.refineCompactPieces
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Fin D.haar.continuous.count → Set (ℚ → M)} (hK : ∀ i, IsCompact (K i))
    (hsub : ∀ i, K i ⊆ (D.haar.continuous.coefficient i).roots)
    (hsmall : (μ.map a) (⋃ i, K i)ᶜ < loss') :
    PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss' where
  haar := D.haar.refine hrecovery hcomplete ha hu hK hsub hsmall
  remainder := by
    intro η hη
    obtain ⟨radius, hpos, hbound⟩ := D.remainder η hη
    exact ⟨radius, hpos, fun i z hz ↦ hbound i z (hsub i hz)⟩

/-- A global compact pressure screen can be installed without changing the
coefficient-piece count or selecting new windows. -/
def PopulationLocalPressureCore.restrictToCompact
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsmall : (μ.map a) (⋃ i : Fin D.haar.continuous.count,
      K ∩ (D.haar.continuous.coefficient i).roots)ᶜ < loss') :
    PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss' :=
  D.refineCompactPieces hrecovery hcomplete ha hu
    (fun i ↦ hK.inter (D.haar.continuous.coefficient i).roots_compact)
    (fun _ ↦ inter_subset_right) hsmall

/-- The selected original root set is exactly the compact screen when that
screen lies in the original core. No root-mass normalization occurs. -/
theorem PopulationLocalPressureCore.restrictToCompact_roots
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ D.haar.continuous.population.roots)
    (hsmall : (μ.map a) (⋃ i : Fin D.haar.continuous.count,
      K ∩ (D.haar.continuous.coefficient i).roots)ᶜ < loss') :
    (D.restrictToCompact hrecovery hcomplete ha hu hK hsmall).haar.continuous.population.roots
      = K := by
  change (⋃ i : Fin D.haar.continuous.count,
    K ∩ (D.haar.continuous.coefficient i).roots) = K
  rw [← inter_iUnion, D.haar.continuous.union_eq, inter_eq_left.mpr hsub]

/-- The SAME actual original closed-window kernel is retained at every retained
root. Refining pressure cores does not condition or recouple either color. -/
theorem PopulationLocalPressureCore.restrictToCompact_closedWindowKernel
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsmall : (μ.map a) (⋃ i : Fin D.haar.continuous.count,
      K ∩ (D.haar.continuous.coefficient i).roots)ᶜ < loss')
    (γ : Kernel (ℚ → M) (ℝ × ℝ))
    (i : Fin D.haar.continuous.count) (z : ℚ → M)
    (hz : z ∈ K ∩ (D.haar.continuous.coefficient i).roots) :
    (D.restrictToCompact hrecovery hcomplete ha hu hK hsmall).originalClosedWindowPairKernel
      hcomplete γ z = D.originalClosedWindowPairKernel hcomplete γ z := by
  have heq := PopulationLocalPressureCore.originalClosedWindowPairKernel_eq_on_piece
    (D.restrictToCompact hrecovery hcomplete ha hu hK hsmall) hcomplete γ i z hz
  rw [heq, D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i z hz.2]
  rfl

/-- Any continuous pressure readout on a retained core has open reference
neighborhoods with uniformly prescribed oscillation. These neighborhoods may
be intersected with the actual geometric neighborhoods before sampling cells. -/
theorem exists_open_pressure_reference_neighborhoods
    {X : Type*} [TopologicalSpace X] {K : Set X} {p : X → ℝ}
    (hp : ContinuousOn p K) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : K → Set X, (∀ ref, IsOpen (V ref) ∧ ref.val ∈ V ref) ∧
      ∀ ref, ∀ z ∈ K ∩ V ref, |p z - p ref.val| < ε := by
  have hneigh (ref : K) : ∃ V : Set X, IsOpen V ∧ ref.val ∈ V ∧
      ∀ z ∈ K ∩ V, |p z - p ref.val| < ε := by
    obtain ⟨V, hV, heq⟩ := continuousOn_iff'.mp hp _ (Metric.isOpen_ball)
    have href : ref.val ∈ p ⁻¹' Metric.ball (p ref.val) ε ∩ K :=
      ⟨Metric.mem_ball_self hε, ref.property⟩
    refine ⟨V, hV, (heq ▸ href).1, ?_⟩
    intro z hz
    have hh : z ∈ p ⁻¹' Metric.ball (p ref.val) ε ∩ K :=
      heq.symm ▸ ⟨hz.2, hz.1⟩
    simpa only [mem_preimage, Metric.mem_ball, Real.dist_eq] using hh.1
  choose V hV hself hosc using hneigh
  exact ⟨V, fun ref ↦ ⟨hV ref, hself ref⟩, hosc⟩

variable [∀ j, (κ j).IsAddHaarMeasure]

/-- All fine-clock comparisons at one original root, with the original Haar
weight and actual retained law. The AE producer below establishes this property
before any finite reference is selected, simultaneously for all real tests t. -/
def OriginalClockClassPressureReferenceGood
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) (hgap : 0 < gap)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (i : Fin D.haar.continuous.count) (z : ℚ → M) : Prop :=
  let C := D.haar.continuous.coefficient i
  let q := finrank ℝ (P C.seedIndex).seed.covector.ker
  let χ := D.originalClosedWindowPairKernel hcomplete γ
  ∀ hz : z ∈ C.roots,
    ∀ (width : ℕ → ℝ) (Q : ∀ n, FiniteScalarBins range (width n)),
    (∀ n, Nonempty (OriginalRangeClockResamplingData C (Q n) z hz f
      (originalUpperRefinementAccuracy n) (originalUpperRefinementAccuracy n))) →
    (∀ n j k, C.clockClassAllowed (Q n) j k →
      ∀ x ∈ (Q n).cell j, ∀ y ∈ (Q n).cell k,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) →
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
          (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 t z))

/-- The actual original conditional laws give one AE set carrying all the
fine-clock pressure readouts on every retained coefficient piece. -/
theorem PopulationLocalPressureCore.ae_original_pressure_reference_good
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
    (hwindowGap : ∀ i, (D.haar.continuous.coefficient i).roots.Nonempty →
      ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap) :
    ∀ᵐ z ∂μ.map a, ∀ i, z ∈ (D.haar.continuous.coefficient i).roots →
      OriginalClockClassPressureReferenceGood γ D hcomplete hδ hδ1 hgap hη f i z := by
  apply ae_all_iff.mpr
  intro i
  exact ae_imp_of_ae_restrict
    (D.ae_original_same_weighted_clockClass_pressure_convergence hrange γ hF hcomplete hu
      ha hinj horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep hδ hδ1 hη f i
      (hwindowGap i))

/-- On the SAME actual original core family, the pressure cutoff, Lusin screen
and all fine-bin reference properties are selected jointly BEFORE references or
iid samples. Every retained root carries the all-tilt comparison, and the actual
signed pressure integral is still bounded by the original global pressure.
The existing zero-tilt integrability input is kept at this analytic layer. -/
theorem eventually_exists_original_pressure_reference_refinement
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
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
    (hγ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z)
      (condDistrib u a μ z) (condDistrib u a ν z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
    (rn : ℕ → ℝ) (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      (rn n) (δn n) (lossn n))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0))
    (hη : ∀ n, 0 ≤ η n ∧ η n < 1)
    (hscreen : ∀ n i, ((D n).haar.continuous.coefficient i).roots.Nonempty →
      (((D n).haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap)
    (f : M × M →ᵇ ℝ)
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f 0)
      (μ.map a))
    (t budget tolerance : ℝ) (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    let χ := fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ
    let p := fun n ↦ originalRetainedFinslerRootPressure P a κ (μ.map a) χ
      (fun n _ ↦ η n) b f n t
    let pref := originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t
    ∀ᶠ n in atTop, ∃ K : Set (ℚ → M), IsCompact K ∧
      K ⊆ (D n).haar.continuous.population.roots ∧
      (μ.map a).real Kᶜ < budget + (lossn n).toReal ∧
      ContinuousOn (p n) K ∧ ContinuousOn pref K ∧
      (∃ B ≥ 0, ∀ z ∈ K, |p n z| ≤ B) ∧
      IntegrableOn (p n) K (μ.map a) ∧
      (∫ z in K, p n z ∂μ.map a) < (∫ z, pref z ∂μ.map a) + tolerance ∧
      ∀ i, ∀ z ∈ K ∩ ((D n).haar.continuous.coefficient i).roots,
        OriginalClockClassPressureReferenceGood γ (D n) hcomplete (hδ n) (hδ1 n)
          hgap (hη n).2 f i z := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let χ := fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ
  let p := fun n ↦ originalRetainedFinslerRootPressure P a κ (μ.map a) χ
    (fun n _ ↦ η n) b f n t
  let pref := originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t
  have hactual := originalClosedWindowPairKernel_ae_mass_recovery γ gap hgap.le rn δn lossn
    D hcomplete hδ hδlim hloss
  have hpressure := originalRetainedFinslerRootPressure_measurable_lower_upper hlaw hF
    hcomplete hu ha hinj hdim hgap hsep γ hγ χ
    (Filter.Eventually.of_forall fun z n ↦ hactual.1 n z) hactual.2 hb f
    (fun n _ ↦ η n) (fun _ ↦ measurable_const)
    (Filter.Eventually.of_forall fun _ ↦ ⟨hηlim, fun n ↦ ⟨(hη n).1, (hη n).2.le⟩⟩) t
  have hpref := (originalPhysicalFinslerRootPressure_measurable_nonneg f hlaw hF hcomplete
    hu ha hinj hdim hgap hsep γ hγ hb t).1
  have hgood n := (D n).ae_original_pressure_reference_good hrange γ hF hcomplete hu ha hinj
    horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep (hδ n) (hδ1 n)
    (hη n).2 f (hscreen n)
  have hcut := eventually_exists_originalClosedWindow_global_pressure_cutoff_on_core
    hlaw hF hcomplete hu ha hinj hdim γ hγ hgap hsep hb rn δn lossn D
    hδ hδlim hloss η hηlim (fun n ↦ ⟨(hη n).1, (hη n).2.le⟩) f hp0
    t (budget / 2) (tolerance / 2) (half_pos hbudget) (half_pos htolerance)
  filter_upwards [hcut] with n hn
  obtain ⟨H, hH, hHsub, hmassH, hpH, hintH⟩ := hn
  have hlower : ∀ᵐ z ∂(μ.map a).restrict H, -(|t| * ‖f‖) ≤ p n z :=
    ae_restrict_of_ae (hpressure.2.mono fun _ h ↦ h.1 n)
  obtain ⟨K, hKH, hK, hmass, hcont, hcontref, hall, hpK, hintK⟩ :=
    exists_compact_pressure_reference_screen (μ.map a) hH hpH hpref
      (ae_restrict_of_ae (hgood n)) (by positivity : 0 ≤ |t| * ‖f‖) hlower
      (half_pos hbudget) (half_pos htolerance)
  have hmassK : (μ.map a).real Kᶜ < budget + (lossn n).toReal := by
    have hcover : Kᶜ ⊆ Hᶜ ∪ (H \ K) := by
      intro z hz
      by_cases hzH : z ∈ H
      · exact Or.inr ⟨hzH, hz⟩
      · exact Or.inl hzH
    have hh := (measureReal_mono (μ := μ.map a) hcover
      (measure_ne_top _ _)).trans (measureReal_union_le (μ := μ.map a) _ _)
    linarith
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.abs
  refine ⟨K, hK, hKH.trans hHsub, hmassK, hcont, hcontref,
    ⟨max B 0, le_max_right _ _, fun z hz ↦
      (hB (mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩, hpK, ?_, ?_⟩
  · change (∫ z in K, p n z ∂μ.map a) < _
    linarith
  · intro i z hz
    exact hall z hz.1 i hz.2

/-- Install a compact pressure screen using its original complement-mass bound. -/
def PopulationLocalPressureCore.restrictToPressureScreen
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ D.haar.continuous.population.roots)
    (hsmall : (μ.map a) Kᶜ < loss') :
    PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss' :=
  D.restrictToCompact hrecovery hcomplete ha hu hK (by
    rw [← inter_iUnion, D.haar.continuous.union_eq, inter_eq_left.mpr hsub]
    exact hsmall)

/-- The screened core has exactly its original compact pressure-screen roots. -/
theorem PopulationLocalPressureCore.restrictToPressureScreen_roots
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ D.haar.continuous.population.roots)
    (hsmall : (μ.map a) Kᶜ < loss') :
    (D.restrictToPressureScreen hrecovery hcomplete ha hu
      hK hsub hsmall).haar.continuous.population.roots = K :=
  D.restrictToCompact_roots hrecovery hcomplete ha hu hK hsub _

/-- Every finite reference subsequently sampled in a screened coefficient piece
lies in the SAME pressure screen. This applies to every cell count and reference
family, and does not assert a property of references chosen before screening. -/
theorem PopulationLocalPressureCore.pressureScreen_reference_mem
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ D.haar.continuous.population.roots)
    (hsmall : (μ.map a) Kᶜ < loss')
    (N : Fin D.haar.continuous.count → ℕ)
    (ref : ∀ i, Fin (N i) →
      ((D.restrictToPressureScreen hrecovery hcomplete ha hu
        hK hsub hsmall).haar.continuous.coefficient i).roots) :
    ∀ i j, (ref i j).val ∈ K := fun i j ↦ (ref i j).property.1

/-- The true original uniform-atlas factory may be used AFTER a compact pressure
screen and open pressure neighborhoods have been selected. Its atlas type and all
repair constants precede every core, screen, fine clock partition and finite
reference. The SAME Q/U witnesses retain resampling, pressure oscillation and the
original full-iid sharp and unit-density upper packets. -/
theorem exists_uniform_original_pressure_reference_factory
    [∀ j, SigmaFinite (κ j)]
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
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
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    (hI : IsCompact I) (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hdim : 6 ≤ finrank ℝ E) :
    ∃ (T : Type (max u₁ u₂)) (hT : Fintype T) (quadC Bnd forwardGap : ℝ),
      let _inst : Fintype T := hT
      0 ≤ quadC ∧ 0 ≤ Bnd ∧ 0 < forwardGap ∧
      ∀ (δ loss loss' : ℝ≥0∞)
      (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
        (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
      (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
      (K : Set (ℚ → M)) (hK : IsCompact K)
      (hsub : K ⊆ D.haar.continuous.population.roots) (hsmall : (μ.map a) Kᶜ < loss')
      (p : (ℚ → M) → ℝ) (hp : ContinuousOn p K)
      (hscreen : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
      (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
      (retention splitError : ℝ) (hretention : 0 < retention)
      (hretention1 : retention < 1) (hsplit : 0 < splitError)
      (f : M × M →ᵇ ℝ) (ε probeError oscillation : ℝ)
      (hε : 0 < ε) (hε1 : ε ≤ 1) (hprobeError : 0 < probeError)
      (_hsmallGeometry : 3 * ε + 2 * ε ^ 2 < 1) (_hoscillation : 0 < oscillation),
      let D' := D.restrictToPressureScreen hrecovery hcomplete ha
        (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)
        hK hsub hsmall
      ∃ (Q : ∀ i : Fin D'.haar.continuous.count,
        (D'.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
        (U : ∀ i : Fin D'.haar.continuous.count,
        (D'.haar.continuous.coefficient i).roots → Set (ℚ → M)),
        (∀ i (ref : (D'.haar.continuous.coefficient i).roots), ref.val ∈ K) ∧
        (∀ i ref, Nonempty (OriginalRangeClockResamplingData (D'.haar.continuous.coefficient i)
          (Q i ref) ref.val ref.property f ε probeError)) ∧
        (∀ i ref, IsOpen (U i ref) ∧ ref.val ∈ U i ref) ∧
        (∀ i ref, ∀ z ∈ (D'.haar.continuous.coefficient i).roots ∩ U i ref,
          |p z - p ref.val| < oscillation) ∧
        (∀ i ref j k, (D'.haar.continuous.coefficient i).clockClassAllowed (Q i ref) j k →
          ∀ s ∈ (Q i ref).cell j, ∀ t ∈ (Q i ref).cell k,
            s ∈ Icc ((D'.haar.continuous.coefficient i).window.val.1 : ℝ)
              (D'.haar.continuous.coefficient i).window.val.2.1 ∧
            t ∈ Icc ((D'.haar.continuous.coefficient i).window.val.1 : ℝ)
              (D'.haar.continuous.coefficient i).window.val.2.1 ∧ s < t) ∧
        D'.originalFixedAtlasSharpPopulationData γ gap Q U retention splitError f ε probeError
          ha T quadC Bnd forwardGap ∧
        D'.originalFixedAtlasUnitDensityPressureData γ gap Q U retention splitError
          f ε probeError (quadC * dyadicMatchingConstant (Module.finrank ℝ E - 1) *
            (Fintype.card T : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨T, hT, quadC, Bnd, forwardGap, hquad, hBnd, hfgap, hfactory⟩ :=
    exists_uniform_original_sharp_population_factory (P := P) (κ := κ)
      (ρ₀ := ρ₀) (ρ₁ := ρ₁) (v := v) (r := r) γ gap hF hcomplete hu ha hinj horder
      hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB πOriginal hπOriginal hcalOriginal
      hI hgap (by omega)
  let _instT : Fintype T := hT
  refine ⟨T, hT, quadC, Bnd, forwardGap, hquad, hBnd, hfgap, ?_⟩
  intro δ loss loss' D hrecovery K hK hsub hsmall p hp hscreen hδ hδ1
    retention splitError hretention hretention1 hsplit f ε probeError oscillation
    hε hε1 hprobeError hsmallGeometry hoscillation
  let D' := D.restrictToPressureScreen hrecovery hcomplete ha hu.continuous.measurable
    hK hsub hsmall
  have hgeometry i := D'.exists_original_clockClass_geometry_with_resampling hF hcomplete hu
    ha hinj i f hgap hsep (hscreen i) hI hgap hε hε1 hprobeError
  choose Q U hRdata hfull hU houter hregion hgeometry using hgeometry
  have hpressure i : ContinuousOn p (D'.haar.continuous.coefficient i).roots :=
    hp.mono inter_subset_left
  choose V hV hosc using fun i ↦
    exists_open_pressure_reference_neighborhoods (hpressure i) hoscillation
  let U' := fun i ref ↦ U i ref ∩ V i ref
  have hUopen i ref : IsOpen (U' i ref) := (hU i ref).1.inter (hV i ref).1
  have hUself i ref : ref.val ∈ U' i ref := ⟨(hU i ref).2, (hV i ref).2⟩
  have hsharp := hfactory δ loss' D' Q U' hUopen hUself houter
    (fun i ref z hz z' hz' s hs t ht hst hA hB ↦
      hregion i ref z ⟨hz.1, hz.2.1⟩ z' ⟨hz'.1, hz'.2.1⟩ s hs t ht hst hA hB)
    hδ hδ1 retention splitError hretention hretention1 hsplit f
    (by positivity : 0 ≤ 3 * ε + 2 * ε ^ 2) hprobeError.le
    (fun i ref z hz z' hz' j k hjk s hs t ht hA hB ↦
      hgeometry i ref z ⟨hz.1, hz.2.1⟩ z' ⟨hz'.1, hz'.2.1⟩ j k hjk s hs t ht hA hB)
    hsmallGeometry
  have hunit := D'.originalFixedAtlasSharpPopulationData_unit_density γ gap Q U'
    retention splitError f ε probeError ha hF hcomplete hu hinj hb hμinv hνinv
    hlabel (fun j ↦ inferInstance) hdim quadC Bnd forwardGap hsharp
  refine ⟨Q, U', fun i ref ↦ ref.property.1, hRdata,
    fun i ref ↦ ⟨hUopen i ref, hUself i ref⟩, ?_, hfull, hsharp, hunit⟩
  intro i ref z hz
  exact hosc i ref z ⟨hz.1, hz.2.2⟩

/-- Restricting coefficient roots preserves its already produced original
continuous-clock resampling certificate in both original scalar coordinates. -/
def OriginalRangeClockResamplingData.forOriginalRoots
    {C : OriginalPopulationCoefficientCore P a κ (μ.map a) μ ν δ}
    {K : Set (ℚ → M)} (hK : IsCompact K) (hsub : K ⊆ C.roots)
    {I : Set ℝ} {width : ℝ} {Q : FiniteScalarBins I width}
    {z : ℚ → M} (hz : z ∈ K) {f : M × M →ᵇ ℝ} {ε probeError : ℝ}
    (Rdata : OriginalRangeClockResamplingData (C.restrictRoots hK hsub)
      Q z hz f ε probeError) :
    OriginalRangeClockResamplingData C Q z (hsub hz) f ε probeError := by
  rcases Rdata with ⟨A, hA, hnonneg, hbound, hrelative, hprobe⟩
  exact ⟨A, hA, hnonneg, hbound, hrelative, hprobe⟩

/-- The exact physical retained pressure also agrees after pressure screening,
with the original inverse intensity and unchanged scalar retention. -/
theorem PopulationLocalPressureCore.pressureScreen_retained_pressure_eq
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ D.haar.continuous.population.roots) (hsmall : (μ.map a) Kᶜ < loss')
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ]
    (f : M × M →ᵇ ℝ) (η t : ℝ)
    (i : Fin D.haar.continuous.count) (z : ℚ → M)
    (hz : z ∈ K ∩ (D.haar.continuous.coefficient i).roots) :
    let D' := D.restrictToPressureScreen hrecovery hcomplete ha hu hK hsub hsmall
    originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun _ ↦ D'.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t z =
    originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t z := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let D' := D.restrictToPressureScreen hrecovery hcomplete ha hu hK hsub hsmall
  have hk := D.restrictToCompact_closedWindowKernel hrecovery hcomplete ha hu hK
    (show (μ.map a) (⋃ i : Fin D.haar.continuous.count,
      K ∩ (D.haar.continuous.coefficient i).roots)ᶜ < loss' from
      by rw [← inter_iUnion, D.haar.continuous.union_eq, inter_eq_left.mpr hsub]; exact hsmall)
    γ i z hz
  have hpressure := originalSeedRetainedRootPressure_congr_at_root
    (P (D.haar.continuous.coefficient i).seedIndex).seed a
    (D'.originalClosedWindowPairKernel hcomplete γ)
    (D.originalClosedWindowPairKernel hcomplete γ) b f z hk
  have hk' : D'.originalClosedWindowPairKernel hcomplete γ z =
      D.originalClosedWindowPairKernel hcomplete γ z := hk
  have hleft := originalRetainedFinslerRootPressure_eq_on_piece P a κ (μ.map a)
    (fun _ ↦ D'.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0
    (D.haar.continuous.coefficient i).seedIndex t
    ((D.haar.continuous.coefficient i).roots_subset_piece hz.2)
  have hright := originalRetainedFinslerRootPressure_eq_on_piece P a κ (μ.map a)
    (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0
    (D.haar.continuous.coefficient i).seedIndex t
    ((D.haar.continuous.coefficient i).roots_subset_piece hz.2)
  apply hleft.trans
  apply Eq.trans _ hright.symm
  simp only [originalRetainedSeedPhysicalPressure, originalRetainedNormalizedPressure]
  rw [hk', hpressure]

/-- Every screened reference inherits the SAME all-Q, all-tilt pressure readout
from its original core. The actual fine models and retained pressure are unchanged;
no new almost-everywhere set is selected after references are chosen. -/
theorem PopulationLocalPressureCore.pressureScreen_reference_good
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ D.haar.continuous.population.roots) (hsmall : (μ.map a) Kᶜ < loss')
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) (hgap : 0 < gap)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (hgood : ∀ i, ∀ z ∈ K ∩ (D.haar.continuous.coefficient i).roots,
      OriginalClockClassPressureReferenceGood γ D hcomplete hδ hδ1 hgap hη f i z) :
    let D' := D.restrictToPressureScreen hrecovery hcomplete ha hu hK hsub hsmall
    ∀ i, ∀ z ∈ (D'.haar.continuous.coefficient i).roots,
      OriginalClockClassPressureReferenceGood γ D' hcomplete hδ hδ1 hgap hη f i z := by
  let D' := D.restrictToPressureScreen hrecovery hcomplete ha hu hK hsub hsmall
  change ∀ i, ∀ z ∈ (D'.haar.continuous.coefficient i).roots,
    OriginalClockClassPressureReferenceGood γ D' hcomplete hδ hδ1 hgap hη f i z
  intro i z hz hz' width Q hRdata hfull
  have hRold n : Nonempty (OriginalRangeClockResamplingData (D.haar.continuous.coefficient i)
      (Q n) z hz'.2 f (originalUpperRefinementAccuracy n)
        (originalUpperRefinementAccuracy n)) := by
    obtain ⟨Rdata⟩ := hRdata n
    exact ⟨Rdata.forOriginalRoots
      (hK.inter (D.haar.continuous.coefficient i).roots_compact) inter_subset_right hz'⟩
  obtain ⟨pref, hlimit, hconv⟩ := hgood i z hz hz'.2 width Q hRold hfull
  refine ⟨pref, hlimit, ?_⟩
  dsimp only
  intro t
  have htarget := D.pressureScreen_retained_pressure_eq hrecovery hcomplete ha hu
    hK hsub hsmall γ f η t i z hz
  rw [htarget]
  exact hconv t

/-- Choose the fine-clock accuracy at EVERY screened root before taking any
finite reference cover. The chosen accuracy may depend on the root; measurability
of this auxiliary choice is unnecessary because the subsequent references are
finite. This avoids evaluating a pointwise limit on arbitrarily moving references. -/
theorem PopulationLocalPressureCore.exists_fine_pressure_reference_choice
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) (hgap : 0 < gap)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (i : Fin D.haar.continuous.count)
    (hgood : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      OriginalClockClassPressureReferenceGood γ D hcomplete hδ hδ1 hgap hη f i z)
    (Q : ∀ _n : ℕ, (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
    (hRdata : ∀ n ref, Nonempty (OriginalRangeClockResamplingData
      (D.haar.continuous.coefficient i) (Q n ref) ref.val ref.property f
      (originalUpperRefinementAccuracy n) (originalUpperRefinementAccuracy n)))
    (hfull : ∀ n ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q n ref) j k →
      ∀ x ∈ (Q n ref).cell j, ∀ y ∈ (Q n ref).cell k,
        x ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        y ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧ x < y)
    (t ε probeError tolerance : ℝ) (hε : 0 < ε) (hprobe : 0 < probeError)
    (htolerance : 0 < tolerance) :
    let C := D.haar.continuous.coefficient i
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let χ := D.originalClosedWindowPairKernel hcomplete γ
    ∃ select : C.roots → ℕ, ∃ pref : C.roots → ℕ → ℝ → ℝ,
      (∀ ref n s, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ref (Q n ref)
        hη hgap.le hδ hδ1 f R s) atTop (𝓝 (pref ref n s))) ∧
      ∀ ref, originalUpperRefinementAccuracy (select ref) < ε ∧
        originalUpperRefinementAccuracy (select ref) < probeError ∧
        let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex ref.val
        let density :=
          (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
          (clockClassPairMeasure
            (D.originalWindowReferenceWeights γ gap I i ref (Q (select ref) ref) η)).real univ
        theta⁻¹ * density ^ (1-2/(q:ℝ)) *
          pref ref (select ref) (t * density ^ (2/(q:ℝ))) <
          originalRetainedFinslerRootPressure P a κ (μ.map a)
            (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 t ref.val + tolerance := by
  let C := D.haar.continuous.coefficient i
  have hroot (ref : C.roots) := hgood ref.val ref.property ref.property
    (fun _ ↦ gap) (fun n ↦ Q n ref) (fun n ↦ hRdata n ref) (fun n ↦ hfull n ref)
  choose pref hlimit hconv using hroot
  have hchoice (ref : C.roots) : ∃ n,
      originalUpperRefinementAccuracy n < ε ∧
      originalUpperRefinementAccuracy n < probeError ∧
      let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex ref.val
      let density :=
        (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
        (clockClassPairMeasure
          (D.originalWindowReferenceWeights γ gap I i ref (Q n ref) η)).real univ
      theta⁻¹ * density ^ (1-2/(finrank ℝ (P C.seedIndex).seed.covector.ker:ℝ)) *
        pref ref n (t * density ^ (2/(finrank ℝ (P C.seedIndex).seed.covector.ker:ℝ))) <
        originalRetainedFinslerRootPressure P a κ (μ.map a)
          (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t ref.val +
          tolerance := by
    have hεev := tendsto_originalUpperRefinementAccuracy.eventually_lt_const hε
    have hprobeev := tendsto_originalUpperRefinementAccuracy.eventually_lt_const hprobe
    have hpressureev := (hconv ref t).eventually_lt_const
      (lt_add_of_pos_right _ htolerance)
    exact (hεev.and (hprobeev.and hpressureev)).exists
  choose select hselect using hchoice
  exact ⟨select, pref, hlimit, hselect⟩

/-- Literal Haar-weighted finite-reference pressure per original root mass.
The coordinate intensity, retained class weights and physical tilt are exact. -/
def PopulationLocalPressureCore.originalWeightedReferencePressure
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    (Q : FiniteScalarBins I gap) (η : ℝ) (pref : ℝ → ℝ) (t : ℝ) : ℝ :=
  let C := D.haar.continuous.coefficient i
  let q := finrank ℝ (P C.seedIndex).seed.covector.ker
  let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex ref.val
  let density :=
    (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
      (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap I i ref Q η)).real univ
  theta⁻¹ * density ^ (1-2/(q:ℝ)) * pref (t * density ^ (2/(q:ℝ)))

/-- Actual original full-clock resampling supplies pressure-accurate finite models
at every screened root. These Q choices precede finite reference sampling; neither
class-pressure convergence nor pressure identification is supplied as an assumption. -/
theorem PopulationLocalPressureCore.exists_pressure_accurate_reference_models
    {I : Set ℝ} (hI : IsCompact I)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) (hgap : 0 < gap)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (i : Fin D.haar.continuous.count)
    (hgood : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      OriginalClockClassPressureReferenceGood γ D hcomplete hδ hδ1 hgap hη f i z)
    (t ε probeError tolerance : ℝ) (hε : 0 < ε) (hprobe : 0 < probeError)
    (htolerance : 0 < tolerance) :
    let C := D.haar.continuous.coefficient i
    ∃ (Q : C.roots → FiniteScalarBins I gap) (select : C.roots → ℕ)
      (pref : C.roots → ℝ → ℝ),
      ∀ ref, originalUpperRefinementAccuracy (select ref) < ε ∧
        originalUpperRefinementAccuracy (select ref) < probeError ∧
        Nonempty (OriginalRangeClockResamplingData C (Q ref) ref.val ref.property f
          (originalUpperRefinementAccuracy (select ref))
          (originalUpperRefinementAccuracy (select ref))) ∧
        (∀ j k, C.clockClassAllowed (Q ref) j k →
          ∀ x ∈ (Q ref).cell j, ∀ y ∈ (Q ref).cell k,
            x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
            y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) ∧
        (∀ s, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ref (Q ref)
          hη hgap.le hδ hδ1 f R s) atTop (𝓝 (pref ref s))) ∧
        D.originalWeightedReferencePressure γ i ref (Q ref) η (pref ref) t <
          originalRetainedFinslerRootPressure P a κ (μ.map a)
            (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t ref.val +
            tolerance := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  have hmodel (n : ℕ) (ref : C.roots) := C.exists_original_full_clock_resampling_data
    hF hcomplete hu ha hinj ref.val ref.property f hI hgap
    (originalUpperRefinementAccuracy_pos_lt_one n).1
    (originalUpperRefinementAccuracy_pos_lt_one n).2.le
    (originalUpperRefinementAccuracy_pos_lt_one n).1
  choose Q hRdata hfull using hmodel
  obtain ⟨select, pref, hlimit, hchoice⟩ := D.exists_fine_pressure_reference_choice γ
    hcomplete hδ hδ1 hgap hη f i hgood Q hRdata hfull t ε probeError tolerance
    hε hprobe htolerance
  refine ⟨fun ref ↦ Q (select ref) ref, select, fun ref ↦ pref ref (select ref), ?_⟩
  intro ref
  exact ⟨(hchoice ref).1, (hchoice ref).2.1, hRdata (select ref) ref,
    hfull (select ref) ref, hlimit ref (select ref), (hchoice ref).2.2⟩

/-- One increasing refinement subsequence synchronizes shrinking pressure cutoffs,
Lusin screens and all future fine-clock references. Its original root losses tend
to zero and its actual retained pressure integrals have vanishing additive error.
The same underlying D family and original root law are preserved. -/
theorem exists_original_diagonal_pressure_reference_screens
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
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
    (hγ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z)
      (condDistrib u a μ z) (condDistrib u a ν z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
    (rn : ℕ → ℝ) (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      (rn n) (δn n) (lossn n))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0))
    (hη : ∀ n, 0 ≤ η n ∧ η n < 1)
    (hscreen : ∀ n i, ((D n).haar.continuous.coefficient i).roots.Nonempty →
      (((D n).haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap)
    (f : M × M →ᵇ ℝ)
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f 0)
      (μ.map a))
    (t : ℝ) :
    let χ := fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ
    let p := fun n ↦ originalRetainedFinslerRootPressure P a κ (μ.map a) χ
      (fun n _ ↦ η n) b f n t
    let pref := originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ K : ℕ → Set (ℚ → M),
      (∀ m, IsCompact (K m) ∧ K m ⊆ (D (φ m)).haar.continuous.population.roots ∧
        (μ.map a).real (K m)ᶜ < originalUpperRefinementAccuracy m ∧
        (δn (φ m)).toReal < originalUpperRefinementAccuracy m ∧
        η (φ m) < originalUpperRefinementAccuracy m ∧
        ContinuousOn (p (φ m)) (K m) ∧ ContinuousOn pref (K m) ∧
        (∃ B ≥ 0, ∀ z ∈ K m, |p (φ m) z| ≤ B) ∧
        IntegrableOn (p (φ m)) (K m) (μ.map a) ∧
        (∫ z in K m, p (φ m) z ∂μ.map a) <
          (∫ z, pref z ∂μ.map a) + originalUpperRefinementAccuracy m ∧
        ∀ i, ∀ z ∈ K m ∩ ((D (φ m)).haar.continuous.coefficient i).roots,
          OriginalClockClassPressureReferenceGood γ (D (φ m)) hcomplete
            (hδ (φ m)) (hδ1 (φ m)) hgap (hη (φ m)).2 f i z) ∧
      Tendsto (fun m ↦ (μ.map a).real (K m)ᶜ) atTop (𝓝 0) ∧
      let residual := fun m ↦
        (ENNReal.ofReal (η (φ m) + originalUpperRefinementAccuracy m +
          (δn (φ m)).toReal) + (μ.map a) (K m)ᶜ).toReal
      (∀ m, 0 ≤ residual m ∧ residual m ≤ 4 * originalUpperRefinementAccuracy m) ∧
      ∀ A tilt : ℝ, Tendsto (fun m ↦ originalUniformUpperError (finrank ℝ E - 1)
        A tilt ‖f‖ (originalUpperRefinementAccuracy m / 10)
        (originalUpperRefinementAccuracy m) (residual m)) atTop (𝓝 0) := by
  have hlosslim : Tendsto (fun n ↦ (lossn n).toReal) atTop (𝓝 0) :=
    (ENNReal.summable_toReal hloss).tendsto_atTop_zero
  have hstep m := eventually_exists_original_pressure_reference_refinement hrange γ hlaw hF
    hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep hγ
    rn δn lossn D hδ hδ1 hδlim hloss η hηlim hη hscreen f hp0 t
    (originalUpperRefinementAccuracy m / 2) (originalUpperRefinementAccuracy m)
    (half_pos (originalUpperRefinementAccuracy_pos_lt_one m).1)
    (originalUpperRefinementAccuracy_pos_lt_one m).1
  have hsmallStep m := (hδlim.eventually_lt_const
    (originalUpperRefinementAccuracy_pos_lt_one m).1).and
    ((hηlim.eventually_lt_const (originalUpperRefinementAccuracy_pos_lt_one m).1).and
      (hlosslim.eventually_lt_const (half_pos (originalUpperRefinementAccuracy_pos_lt_one m).1)))
  have hjoint m := (hstep m).and (hsmallStep m)
  obtain ⟨φ, hφ, hchoice⟩ := extraction_forall_of_eventually hjoint
  have hscreenChoice m := (hchoice m).1
  choose K hK hsub hmass hcont hcontref hbounded hI hint hgood using hscreenChoice
  have hmass' m : (μ.map a).real (K m)ᶜ < originalUpperRefinementAccuracy m := by
    have hh := (hchoice m).2.2.2
    linarith only [hmass m, hh]
  have hRbound m : 0 ≤
      (ENNReal.ofReal (η (φ m) + originalUpperRefinementAccuracy m +
        (δn (φ m)).toReal) + (μ.map a) (K m)ᶜ).toReal ∧
      (ENNReal.ofReal (η (φ m) + originalUpperRefinementAccuracy m +
        (δn (φ m)).toReal) + (μ.map a) (K m)ᶜ).toReal ≤
        4 * originalUpperRefinementAccuracy m := by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top _ _),
      ENNReal.toReal_ofReal (add_nonneg
        (add_nonneg (hη (φ m)).1 (originalUpperRefinementAccuracy_pos_lt_one m).1.le)
        ENNReal.toReal_nonneg)]
    have hd := (hchoice m).2.1
    have he := (hchoice m).2.2.1
    change η (φ m) + originalUpperRefinementAccuracy m +
      (δn (φ m)).toReal + (μ.map a).real (K m)ᶜ ≤ _
    linarith only [hd, he, hmass' m]
  refine ⟨φ, hφ, K, fun m ↦
    ⟨hK m, hsub m, hmass' m, (hchoice m).2.1, (hchoice m).2.2.1,
      hcont m, hcontref m, hbounded m, hI m, hint m, hgood m⟩,
    squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg) (fun m ↦ (hmass' m).le)
      tendsto_originalUpperRefinementAccuracy, hRbound, ?_⟩
  intro A tilt
  exact tendsto_original_uniform_upper_errors (finrank ℝ E - 1) (by omega) A tilt ‖f‖
    (fun m ↦ (ENNReal.ofReal (η (φ m) + originalUpperRefinementAccuracy m +
      (δn (φ m)).toReal) + (μ.map a) (K m)ᶜ).toReal) hRbound

end OTSelector.Reconstruction
