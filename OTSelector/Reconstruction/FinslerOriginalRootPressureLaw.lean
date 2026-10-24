import OTSelector.Reconstruction.FinslerOriginalRootPressure
import OTSelector.Reconstruction.OriginalFocalWindowPressureUpper
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalFullScene

/-! Original physical conditional moments and separation produce the canonical
true pressure on every selected original seed piece, with one physical probe norm. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]

/-- The actual original physical moment and separation laws construct the
canonical thermodynamic pressure on each original seed piece. Its true limit,
common physical probe Lipschitz constant and probe lower bound are internal;
no root pressure, regularity or optimizer-selection callback is supplied. -/
theorem PopulationSeedPieceMomentLaw.ae_originalSeedRootPressure_limits
    (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hdim : 6 ≤ finrank ℝ E)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diameter)
    (γ : Kernel Z (ℝ × ℝ)) [IsMarkovKernel γ]
    (hγ : ∀ᵐ z ∂lambda, Vlasov.IsCoupling (γ z)
      (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
    {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ) (j : ℕ) :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      (∀ t, Tendsto (fun R : ℝ ↦ originalSeedRootScalePressure (P j).seed a η₀ η₁ b f R t z)
        atTop (𝓝 (originalSeedRootPressure (P j).seed a η₀ η₁ b f z t))) ∧
      LipschitzWith ‖f‖₊ (originalSeedRootPressure (P j).seed a η₀ η₁ b f z) ∧
      ∀ t, -(|t| * ‖f‖) ≤ originalSeedRootPressure (P j).seed a η₀ η₁ b f z t := by
  filter_upwards [ae_restrict_of_ae hlaw,ae_restrict_of_ae hsep,ae_restrict_of_ae hγ,
    ae_restrict_mem (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)]
    with z hz hsz hγz hzpiece
  let w := populationSeedPieceLabel P a κ lambda j ⟨z,hzpiece⟩
  obtain ⟨D⟩ := hz j hzpiece
  let S := (P j).seed
  let g := originalPhysicalRootProbe b f z
  have hg : Measurable (uncurry g) :=
    (measurable_originalPhysicalRootProbe hcomplete hb f).comp measurable_prodMk_left
  have hgb x y : |g x y| ≤ ‖f‖ := by
    exact (f.norm_coe_le_norm (b (z,x),b (z,y)))
  have hq : 4 < finrank ℝ S.covector.ker := by
    have h := S.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    omega
  obtain ⟨p,hp,hconc,hLip,hscene⟩ := D.exists_stationary_original_focal_fullInput_scene
    hF w.property hq hgap hsz (γ z) hγz.1 hγz.2 (norm_nonneg f) hg hgb
  have hkin : originalSeedRootKinetic S a z =
      fun x y v ↦ matrixQuadratic (originalSeedPairCoefficient S w (x,y)) v := by
    funext x y v
    exact congrArg (fun A ↦ matrixQuadratic A v)
      (populationSeedRootCoefficient_eq_pieceCoefficient P a κ lambda hF hcomplete hu ha hinj
        j hzpiece (x,y))
  have hscale (R t : ℝ) : originalSeedRootScalePressure S a η₀ η₁ b f R t z =
      legalMarkedScalePressure (finrank ℝ S.covector.ker) id id
        (condDistrib u a η₀ z) (condDistrib u a η₁ z) (D.originalFocalKinetic gap) g R t := by
    unfold originalSeedRootScalePressure
    rw [hkin]
    exact (D.original_focal_scalePressure_eq_actual_coefficient hsz
      (condDistrib u a η₀ z) (condDistrib u a η₁ z)
      Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl g R t).symm
  have hlim t : Tendsto (fun R : ℝ ↦ originalSeedRootScalePressure S a η₀ η₁ b f R t z)
      atTop (𝓝 (p t)) := (hp t).congr' (Filter.Eventually.of_forall (fun R ↦ (hscale R t).symm))
  have heq t : originalSeedRootPressure S a η₀ η₁ b f z t = p t := (hlim t).limUnder_eq
  have hzero : 0 ≤ p 0 := by
    obtain ⟨C,hC,hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF w.property hgap hsz
    apply ge_of_tendsto (hp 0)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simpa only [abs_zero,zero_mul,neg_zero] using legalMarkedScalePressure_lower_bound
      (finrank ℝ S.covector.ker) measurable_id measurable_id
      (condDistrib u a η₀ z) (condDistrib u a η₁ z) hC (norm_nonneg f)
      (D.measurable_originalFocalKinetic hF w.property gap)
      (D.originalFocalKinetic_nonneg hF w.property hgap) hkb hg hgb 0 hR
  have heqfun : originalSeedRootPressure S a η₀ η₁ b f z = p := funext heq
  refine ⟨?_,?_,?_⟩
  · intro t
    change Tendsto (fun R : ℝ ↦ originalSeedRootScalePressure S a η₀ η₁ b f R t z)
      atTop (𝓝 (originalSeedRootPressure S a η₀ η₁ b f z t))
    rw [heq]
    exact hlim t
  · rw [heqfun]
    exact hLip
  · intro t
    have h := hLip.dist_le_mul t 0
    simp only [Real.dist_eq,sub_zero] at h
    change |p t - p 0| ≤ ‖f‖ * |t| at h
    rw [heq]
    nlinarith only [(abs_le.mp h).1,hzero]

end OTSelector.Reconstruction
