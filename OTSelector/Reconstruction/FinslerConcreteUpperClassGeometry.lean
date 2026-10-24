import OTSelector.Reconstruction.FinslerConcreteUpperClassClockGap
import OTSelector.Reconstruction.FinslerCoefficientCoreTaylorCover

/-!
Every original retained root has an open self-neighborhood with actual Taylor,
coefficient and physical-probe control. These neighborhoods are chosen before
any reference-dependent finite class or Hall tolerance cover is selected.
-/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction.PopulationLocalPressureCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- The actual original Taylor error, root freezing, pair-probe oscillation and
seed-coordinate diameter are controlled in one open neighborhood at every
reference root. No finite reference set has yet been chosen. -/
theorem exists_original_pair_geometry_neighborhoods (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M → ℝ) (hf : Continuous f)
    {ε B radius : ℝ} (hε : 0 < ε) (hB : 0 < B) (hradius : 0 < radius) :
    ∃ U : (ℚ → M) → Set (ℚ → M),
      (∀ z₀, IsOpen (U z₀) ∧ z₀ ∈ U z₀) ∧
      ∀ z₀ ∈ (D.haar.continuous.coefficient i).roots,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U z₀,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U z₀,
        let C := D.haar.continuous.coefficient i
        let S := (P C.seedIndex).seed
        let R := populationSeedRootLabelValue S a
        let v := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
        ‖R z - R z'‖ < radius ∧
        (∀ p ∈ C.window.region,
          |populationSeedPairDeficit S p (R z, R z') - matrixQuadratic (C.matrix z₀ p) v| ≤
            2 * ε * matrixQuadratic (C.matrix z₀ p) v) ∧
        ∀ s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
        ∀ t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
          |f (D.corePoint i (z, s), D.corePoint i (z', t)) -
            f (D.corePoint i (z₀, s), D.corePoint i (z₀, t))| ≤ B := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let _instRootMetric : MetricSpace (ℚ → M) := TopologicalSpace.metrizableSpaceMetric (ℚ → M)
  let _instRootUniform : UniformSpace (ℚ → M) := _instRootMetric.toUniformSpace
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let bW := Module.finBasis ℝ S.covector.ker
  let T := Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ)
  have hR : ContinuousOn R C.roots := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).continuous_label
  obtain ⟨m, hm, hlower⟩ := C.exists_quadratic_lower_bound
  obtain ⟨remRadius, hremRadius, hrem⟩ :=
    D.source_remainder_on_piece hF hcomplete hu ha hinj i (ε * m) (mul_pos hε hm)
  obtain ⟨dA, hdA, hA⟩ := exists_uniform_relative_matrixQuadratic
    (C.roots_compact.prod C.window.isCompact_region) C.coefficient_continuous
    (fun q hq ↦ C.coefficient_posDef q.1 hq.1 q.2 hq.2) hε
  have hc : ContinuousOn (fun z ↦ bW.equivFun (R z)) C.roots :=
    bW.equivFunL.continuous.comp_continuousOn hR
  obtain ⟨dc, hdc, hcoords⟩ := Metric.uniformContinuousOn_iff.mp
    (C.roots_compact.uniformContinuousOn_of_continuous hc) remRadius hremRadius
  obtain ⟨dR, hdR, hlabels⟩ := Metric.uniformContinuousOn_iff.mp
    (C.roots_compact.uniformContinuousOn_of_continuous hR) radius hradius
  let probe : ((ℚ → M) × (ℚ → M)) × (ℝ × ℝ) → ℝ := fun q ↦
    f (D.corePoint i (q.1.1, q.2.1), D.corePoint i (q.1.2, q.2.2))
  have hprobe : ContinuousOn probe ((C.roots ×ˢ C.roots) ×ˢ (T ×ˢ T)) := by
    apply hf.comp_continuousOn
    apply ContinuousOn.prodMk
    · exact (D.continuousOn_corePoint i).comp
        (by fun_prop : Continuous (fun q : ((ℚ → M) × (ℚ → M)) × (ℝ × ℝ) ↦
          (q.1.1, q.2.1))).continuousOn (fun q hq ↦ ⟨hq.1.1, hq.2.1⟩)
    · exact (D.continuousOn_corePoint i).comp
        (by fun_prop : Continuous (fun q : ((ℚ → M) × (ℚ → M)) × (ℝ × ℝ) ↦
          (q.1.2, q.2.2))).continuousOn (fun q hq ↦ ⟨hq.1.2, hq.2.2⟩)
  have hcompactProbe : IsCompact ((C.roots ×ˢ C.roots) ×ˢ (T ×ˢ T)) :=
    (C.roots_compact.prod C.roots_compact).prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨dp, hdp, hprobes⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompactProbe.uniformContinuousOn_of_continuous hprobe) B hB
  let d := min dA (min (dc / 2) (min (dR / 2) dp))
  have hd : 0 < d := lt_min hdA (lt_min (half_pos hdc) (lt_min (half_pos hdR) hdp))
  refine ⟨fun z₀ ↦ Metric.ball z₀ d, fun z₀ ↦ ⟨Metric.isOpen_ball, Metric.mem_ball_self hd⟩, ?_⟩
  intro z₀ hz₀ z hz z' hz'
  have hzdA : dist z z₀ < dA := hz.2.trans_le (min_le_left _ _)
  have hzdp : dist z z₀ < dp := hz.2.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hz'dp : dist z' z₀ < dp := hz'.2.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hdiam (s : ℝ) (hds : d ≤ s / 2) : dist z z' < s := by
    have hzdist := hz.2.trans_le hds
    have hz'dist := hz'.2.trans_le hds
    have ht := dist_triangle z z₀ z'
    rw [dist_comm z₀ z'] at ht
    linarith
  have hcoord : ‖bW.equivFun (R z' - R z)‖ < remRadius := by
    have h := hcoords z' hz'.1 z hz.1
      (by rw [dist_comm]; exact hdiam dc ((min_le_right _ _).trans (min_le_left _ _)))
    simpa only [dist_eq_norm, map_sub] using h
  refine ⟨?_, ?_, ?_⟩
  · simpa only [dist_eq_norm] using hlabels z hz.1 z' hz'.1
      (hdiam dR ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  · intro p hp
    have hfreeze := hA (z, p) ⟨hz.1, hp⟩ (z₀, p) ⟨hz₀, hp⟩
      (by simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hzdA)
    let v := bW.equivFun (R z' - R z)
    have heq : R z + bW.equivFun.symm v = R z' := by simp only [v,
      LinearEquiv.symm_apply_apply, add_sub_cancel]
    have htaylor := hrem z hz.1 p hp v hcoord (by
      rw [heq]
      exact C.root_label_mem_window hF hcomplete hu ha hinj hz'.1)
    rw [heq] at htaylor
    have hlow := mul_le_mul_of_nonneg_left (hlower z₀ hz₀ p hp v) hε.le
    have htri := abs_sub_le (populationSeedPairDeficit S p (R z, R z'))
      (matrixQuadratic (C.matrix z p) v) (matrixQuadratic (C.matrix z₀ p) v)
    change |populationSeedPairDeficit S p (R z, R z') - matrixQuadratic (C.matrix z₀ p) v| ≤
      2 * ε * matrixQuadratic (C.matrix z₀ p) v
    change |populationSeedPairDeficit S p (R z, R z') - matrixQuadratic (C.matrix z p) v| ≤
      ε * m * ‖v‖ ^ 2 at htaylor
    have hfreeze' := hfreeze v
    change |matrixQuadratic (C.matrix z p) v - matrixQuadratic (C.matrix z₀ p) v| ≤
      ε * matrixQuadratic (C.matrix z₀ p) v at hfreeze'
    nlinarith only [htaylor, hlow, hfreeze', htri]
  · intro s hs t ht
    have hdist : dist ((z, z'), (s, t)) ((z₀, z₀), (s, t)) < dp := by
      simpa only [Prod.dist_eq, dist_self, max_lt_iff] using
        And.intro (And.intro hzdp hz'dp) hdp
    have h := hprobes ((z, z'), (s, t)) ⟨⟨hz.1, hz'.1⟩, hs, ht⟩
      ((z₀, z₀), (s, t)) ⟨⟨hz₀, hz₀⟩, hs, ht⟩ hdist
    exact (show |probe ((z, z'), (s, t)) - probe ((z₀, z₀), (s, t))| < B by
      simpa only [Real.dist_eq] using h).le


/-- Full original clock bins and open neighborhoods can be chosen at every
reference before taking the finite Hall/class cover. Actual support points in
retained class edges satisfy the true distance/probe comparison with the
literal finite reference model. -/
theorem exists_full_original_clockClass_geometry (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M → ℝ) (hf : Continuous f)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    {I : Set ℝ} (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε probeError : ℝ} (hε : 0 < ε) (hprobeError : 0 < probeError) :
    let C := D.haar.continuous.coefficient i
    ∃ (Q : C.roots → FiniteScalarBins I globalGap) (U : C.roots → Set (ℚ → M)),
      (∀ z₀, IsOpen (U z₀) ∧ z₀.val ∈ U z₀) ∧
      ∀ z₀, ∀ z ∈ C.roots ∩ U z₀, ∀ z' ∈ C.roots ∩ U z₀,
      ∀ j k, C.clockClassAllowed (Q z₀) j k → ∀ s ∈ (Q z₀).cell j,
      ∀ t ∈ (Q z₀).cell k,
      D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        let S := (P C.seedIndex).seed
        let R := populationSeedRootLabelValue S a
        let v := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
        (s, t) ∈ C.window.region ∧
        |populationSeedPairDeficit S (s, t) (R z, R z') -
          C.clockClassKinetic (Q z₀) z₀.val j k v| ≤
            (3 * ε + 2 * ε ^ 2) * C.clockClassKinetic (Q z₀) z₀.val j k v ∧
        |f (D.corePoint i (z, s), D.corePoint i (z', t)) -
          C.clockClassProbe (Q z₀) z₀.val z₀.property f j k| ≤ 2 * probeError := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  obtain ⟨radius, hradius, hregion⟩ := D.exists_original_clock_region_radius hF i hgap hsep hscreen
  obtain ⟨U, hU, hgeometry⟩ := D.exists_original_pair_geometry_neighborhoods hF hcomplete hu ha hinj
    i f hf hε hprobeError hradius
  choose Q hQ using fun z₀ : C.roots ↦ C.exists_full_clockClass_model_with_endpoints
    hF hcomplete hu ha hinj z₀.val z₀.property f hf hI hglobalGap hε hprobeError
  refine ⟨Q, fun z₀ ↦ U z₀.val, fun z₀ ↦ hU z₀.val, ?_⟩
  intro z₀ z hz z' hz' j k hjk s hs t ht hA hB
  obtain ⟨hsI, htI, hhalf, hforward, hkin, hprobe⟩ := hQ z₀ j k hjk s hs t ht
  obtain ⟨hdiam, hcost, hphysicalProbe⟩ := hgeometry z₀.val z₀.property z hz z' hz'
  have hp := hregion z hz.1 z' hz'.1 s hsI t htI hdiam hforward hA hB
  refine ⟨hp, ?_, ?_⟩
  · let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let v := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
    let raw := matrixQuadratic (C.matrix z₀.val (s, t)) v
    let frozen := C.clockClassKinetic (Q z₀) z₀.val j k v
    have hraw_le : raw ≤ (1 + ε) * frozen := by
      have h := (abs_le.mp (hkin v)).2
      dsimp only [raw, frozen]
      linarith
    have hcost' := hcost (s, t) hp
    have hscaled := mul_le_mul_of_nonneg_left hraw_le (by positivity : 0 ≤ 2 * ε)
    have htri := abs_sub_le (populationSeedPairDeficit S (s, t) (R z, R z')) raw frozen
    have hbin := hkin v
    change |populationSeedPairDeficit S (s, t) (R z, R z') - frozen| ≤
      (3 * ε + 2 * ε ^ 2) * frozen
    nlinarith only [hcost', hscaled, htri, hbin]
  · have hreference : originalReferenceClockProbe C z₀.val z₀.property f (s, t) =
        f (D.corePoint i (z₀.val, s), D.corePoint i (z₀.val, t)) := by
      dsimp only [originalReferenceClockProbe, corePoint]
      rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
        ⟨z₀.val, C.roots_subset_piece z₀.property⟩]
    have hphysical := hphysicalProbe s hsI t htI
    rw [← hreference] at hphysical
    have htri := abs_sub_le (f (D.corePoint i (z, s), D.corePoint i (z', t)))
      (originalReferenceClockProbe C z₀.val z₀.property f (s, t))
      (C.clockClassProbe (Q z₀) z₀.val z₀.property f j k)
    linarith

end OTSelector.Reconstruction.PopulationLocalPressureCore
