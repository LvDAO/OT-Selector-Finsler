import OTSelector.Reconstruction.OriginalIIDTaggedPhysicalEnergyLower
import OTSelector.Geometry.FinslerDistanceLocalizationPopulation
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Sharp freezing of the actual bounded continuous physical probe on the same
original rooted Taylor window, with an error paid by actual edge mass. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- A continuous injection on a compact set has a uniform inverse modulus.
The statement also covers the empty compact set. -/
theorem exists_dist_lt_of_compact_continuousOn_injOn
    {Z V : Type*} [MetricSpace Z] [MetricSpace V]
    {K : Set Z} (hK : IsCompact K) (f : Z → V) (hf : ContinuousOn f K)
    (hinj : InjOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ K, ∀ z' ∈ K, dist (f z) (f z') < δ → dist z z' < ε := by
  let bad : Set (Z × Z) := (K ×ˢ K) ∩ {p | ε ≤ dist p.1 p.2}
  have hbad : IsCompact bad := (hK.prod hK).inter_right
    (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
  have hdist : ContinuousOn (fun p : Z × Z ↦ dist (f p.1) (f p.2)) (K ×ˢ K) :=
    continuous_dist.comp_continuousOn
      ((hf.comp continuous_fst.continuousOn (fun (p : Z × Z) (hp : p ∈ K ×ˢ K) ↦ hp.1)).prodMk
        (hf.comp continuous_snd.continuousOn (fun (p : Z × Z) (hp : p ∈ K ×ˢ K) ↦ hp.2)))
  have hpositive (p : Z × Z) (hp : p ∈ bad) : 0 < dist (f p.1) (f p.2) := by
    by_contra hn
    have heq : f p.1 = f p.2 := by
      have hd : dist (f p.1) (f p.2) = 0 := le_antisymm (not_lt.mp hn) dist_nonneg
      exact dist_eq_zero.mp hd
    have hp' : p.1 = p.2 := hinj hp.1.1 hp.1.2 heq
    have hc : ε ≤ dist p.1 p.2 := hp.2
    simp only [hp',dist_self] at hc
    exact (not_le_of_gt hε) hc
  obtain ⟨δ,hδ,hmin⟩ := hbad.exists_forall_le' (hdist.mono inter_subset_left) hpositive
  refine ⟨δ,hδ,?_⟩
  intro z hz z' hz' hd
  by_contra hn
  exact (not_le_of_gt hd) (hmin (z,z') ⟨⟨hz,hz'⟩,not_lt.mp hn⟩)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore

/-- The exact original physical probe frozen only in the original root label;
both actual endpoint clocks are retained. -/
def originalRootedFrozenProbe
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (g : (M × M) →ᵇ ℝ)
    (z : ℚ → M) (p : M × M) : ℝ :=
  g (D.corePoint i (z,u p.1),D.corePoint i (z,u p.2))

/-- Compact original root and clock carriers give an arbitrarily small probe
error on every bounded original rooted window. The oscillation follows from the
actual continuous probe and original label recovery, rather than an input bound. -/
theorem exists_uniform_original_rooted_probe_error
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) (g : (M × M) →ᵇ ℝ)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ U z root p, p ∈ D.originalRootedTaylorWindow i R scale U z root →
        |g p - D.originalRootedFrozenProbe i g z p| ≤ ε := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  letI rootMetric : MetricSpace (ℚ → M) := TopologicalSpace.metrizableSpaceMetric (ℚ → M)
  letI : UniformSpace (ℚ → M) := rootMetric.toUniformSpace
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let w := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let T := Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ)
  let probe : ((ℚ → M) × (ℚ → M)) × (ℝ × ℝ) → ℝ := fun q ↦
    g (D.corePoint i (q.1.1,q.2.1),D.corePoint i (q.1.2,q.2.2))
  have hprobe : ContinuousOn probe ((C.roots ×ˢ C.roots) ×ˢ (T ×ˢ T)) := by
    apply g.continuous.comp_continuousOn
    apply ContinuousOn.prodMk
    · exact (D.continuousOn_corePoint i).comp
        (by fun_prop : Continuous (fun q : ((ℚ → M) × (ℚ → M)) × (ℝ × ℝ) ↦
          (q.1.1,q.2.1))).continuousOn (fun q hq ↦ ⟨hq.1.1,hq.2.1⟩)
    · exact (D.continuousOn_corePoint i).comp
        (by fun_prop : Continuous (fun q : ((ℚ → M) × (ℚ → M)) × (ℝ × ℝ) ↦
          (q.1.2,q.2.2))).continuousOn (fun q hq ↦ ⟨hq.1.2,hq.2.2⟩)
  have hcompact : IsCompact ((C.roots ×ˢ C.roots) ×ˢ (T ×ˢ T)) :=
    (C.roots_compact.prod C.roots_compact).prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨dp,hdp,hprobes⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hprobe) ε hε
  have hw : ContinuousOn w C.roots := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).continuous_label
  have he : ContinuousOn (fun z ↦ e (w z)) C.roots := e.continuous.comp_continuousOn hw
  have hinje : InjOn (fun z ↦ e (w z)) C.roots := by
    intro z hz z' hz' h
    exact fixed_seed_rootLabel_injOn hF hcomplete hu ha hinj C.seedIndex
      (C.roots_subset_piece hz) (C.roots_subset_piece hz') (e.injective h)
  obtain ⟨d,hd,hinverse⟩ := exists_dist_lt_of_compact_continuousOn_injOn
    C.roots_compact (fun z ↦ e (w z)) he hinje hdp
  let threshold := R / d + 1
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs U z root p hp
  rcases hp with ⟨hz,hroot,hx,hy,hxr,hyr,hclock,hxR,hyR,hsource⟩
  have hscale : 0 < scale := hthreshold.trans_le hs
  have hsmall : R / scale < d := by
    have hlt : R / d < scale := by dsimp [threshold] at hs; linarith
    have hm := (div_lt_iff₀ hd).mp hlt
    exact (div_lt_iff₀ hscale).mpr (by nlinarith)
  have hnear (x : M) (hx : a x ∈ C.roots)
      (hxR : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        C.seedIndex scale x - root‖ ≤ R) : dist (a x) z < dp := by
    have hm := dist_physicalSceneOriginalSeedBasisPosition_macro_le
      C.seedIndex scale hscale root x R hxR
    rw [hroot,inv_smul_smul₀ hscale.ne'] at hm
    apply hinverse (a x) hx z hz
    exact hm.trans_lt hsmall
  have hpx := hnear p.1 hx hxR
  have hpy := hnear p.2 hy hyR
  have hclockx : u p.1 ∈ T := (C.window.region_subset hclock).1
  have hclocky : u p.2 ∈ T := (C.window.region_subset hclock).2.1
  have hpdist : dist ((a p.1,a p.2),(u p.1,u p.2)) ((z,z),(u p.1,u p.2)) < dp := by
    simpa only [Prod.dist_eq,dist_self] using max_lt (max_lt hpx hpy) hdp
  have h := hprobes ((a p.1,a p.2),(u p.1,u p.2))
    ⟨⟨hx,hy⟩,⟨hclockx,hclocky⟩⟩ ((z,z),(u p.1,u p.2))
    ⟨⟨hz,hz⟩,⟨hclockx,hclocky⟩⟩ hpdist
  have hxlabel := C.root_label_mem_window hF hcomplete hu ha hinj hx
  have hylabel := C.root_label_mem_window hF hcomplete hu ha hinj hy
  have hxread := C.physical_readout_of_regular hF hcomplete hu ha hinj horder hxr hx hclockx
  have hyread := C.physical_readout_of_regular hF hcomplete hu ha hinj horder hyr hy hclocky
  have hxcurve : D.corePoint i (a p.1,u p.1) = p.1 :=
    (populationSeedPhysicalMap_at_label S ⟨w (a p.1),hxlabel.1⟩ (u p.1)).symm.trans hxread
  have hycurve : D.corePoint i (a p.2,u p.2) = p.2 :=
    (populationSeedPhysicalMap_at_label S ⟨w (a p.2),hylabel.1⟩ (u p.2)).symm.trans hyread
  simpa only [Real.dist_eq,probe,hxcurve,hycurve,originalRootedFrozenProbe] using h.le


/-- The same-root matrix Taylor term and the actual root-frozen probe have an
arbitrarily small joint signed error on the literal original Taylor window. -/
theorem exists_uniform_original_rooted_tilted_error
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ U z root p, p ∈ D.originalRootedTaylorWindow i R scale U z root →
        |(D.originalRootedTaylorKinetic i scale z p + t * D.originalRootedFrozenProbe i g z p) -
          (scale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) + t * g p)| ≤ ε := by
  let η := ε / (|t| + 1)
  have hden : 0 < |t| + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨Tk,hTk,hkin⟩ :=
    D.exists_uniform_original_rooted_taylor_error hF hcomplete hu ha hinj horder i R hR hη
  obtain ⟨Tg,hTg,hprobe⟩ :=
    D.exists_uniform_original_rooted_probe_error hF hcomplete hu ha hinj horder i g R hR hη
  refine ⟨max Tk Tg,lt_max_iff.mpr (Or.inl hTk),?_⟩
  intro scale hs U z root p hp
  have hprobe' := hprobe scale ((le_max_right _ _).trans hs) U z root p hp
  have hk : |D.originalRootedTaylorKinetic i scale z p -
      scale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)| ≤ η := by
    rcases hp with ⟨hz,hroot,hx,hy,hxr,hyr,hclock,hxR,hyR,hsource⟩
    rw [hroot] at hxR hyR
    have h := hkin scale ((le_max_left _ _).trans hs) z hz p.1 p.2
      hx hy hxr hyr hclock hxR hyR
    rw [abs_sub_comm] at h
    convert h using 1
    simp only [originalRootedTaylorKinetic,physicalSceneOriginalSeedScaledPosition,
      physicalSceneOriginalSeedBasisPosition,smul_sub]
    rfl
  have heq :
      (D.originalRootedTaylorKinetic i scale z p + t * D.originalRootedFrozenProbe i g z p) -
        (scale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) + t * g p) =
      (D.originalRootedTaylorKinetic i scale z p -
        scale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) +
        t * (D.originalRootedFrozenProbe i g z p - g p) := by ring
  rw [heq]
  calc
    _ ≤ |D.originalRootedTaylorKinetic i scale z p -
        scale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)| +
        |t * (D.originalRootedFrozenProbe i g z p - g p)| := abs_add_le _ _
    _ ≤ η + |t| * η := by
      rw [abs_mul,abs_sub_comm (D.originalRootedFrozenProbe i g z p)]
      exact add_le_add hk (mul_le_mul_of_nonneg_left hprobe' (abs_nonneg t))
    _ = ε := by
      have he : η * (|t| + 1) = ε := div_mul_cancel₀ ε hden.ne'
      nlinarith

/-- Actual finite Haar-window comparison with the full original matrix and
sharply frozen physical tilt. The sole approximation error is ε times the same
original edge mass, before any atlas sum or limiting passage. -/
theorem exists_uniform_original_rooted_tilted_window_energy_le
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ],
      ∀ (rootDomain U : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet U →
      ∀ (N : ℝ), 0 < N → ∀ ref : D.coreSpatialCoordinateSpace i → (ℚ → M),
      (∫⁻ root, ENNReal.ofReal N *
        (∫⁻ p in D.originalRootedTaylorWindow i R scale U (ref root) root,
          ENNReal.ofReal (D.originalRootedTaylorKinetic i scale (ref root) p +
            t * D.originalRootedFrozenProbe i g (ref root) p + |t| * ‖g‖) ∂Γ)
        ∂cavityRootMeasure volume rootDomain N) ≤
      volume U * ((∫⁻ p, ENNReal.ofReal (scale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) + t * g p + |t| * ‖g‖) ∂Γ) +
          ENNReal.ofReal ε * Γ univ) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨threshold,hthreshold,herror⟩ :=
    D.exists_uniform_original_rooted_tilted_error hF hcomplete hu ha hinj horder i g t R hR hε
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs Γ _ rootDomain U hU N hN ref
  let C := D.haar.continuous.coefficient i
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale
  let base : M × M → ℝ := fun p ↦ scale ^ 2 *
    ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) + t * g p + |t| * ‖g‖
  have hb : Measurable base :=
    (((F.measurable_distance_slack hu).const_mul (scale ^ 2)).add
      (g.continuous.measurable.const_mul t)).add_const _
  have hb0 (p : M × M) : 0 ≤ base p := by
    have h := hu.le_add_mul p.2 p.1
    simp only [NNReal.coe_one,one_mul,dist_comm p.2 p.1] at h
    have hslack : 0 ≤ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1 := by
      change 0 ≤ dist p.1 p.2 - u p.2 + u p.1
      linarith
    have hbound : |t * g p| ≤ |t| * ‖g‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm p) (abs_nonneg t)
    dsimp only [base]
    nlinarith [mul_nonneg (sq_nonneg scale) hslack,(abs_le.mp hbound).1]
  let upper : M × M → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (base p + ε)
  have hupper : Measurable upper := (hb.add_const ε).ennreal_ofReal
  have hcoord : Measurable coord :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ scale
  have hpoint (root : D.coreSpatialCoordinateSpace i) :
      (∫⁻ p in D.originalRootedTaylorWindow i R scale U (ref root) root,
        ENNReal.ofReal (D.originalRootedTaylorKinetic i scale (ref root) p +
          t * D.originalRootedFrozenProbe i g (ref root) p + |t| * ‖g‖) ∂Γ) ≤
      cavityRootWindowReadout Γ (fun p ↦ coord p.1) upper U root := by
    let event := D.originalRootedTaylorWindow i R scale U (ref root) root
    have hbound (p : M × M) (hp : p ∈ event) :
        ENNReal.ofReal (D.originalRootedTaylorKinetic i scale (ref root) p +
          t * D.originalRootedFrozenProbe i g (ref root) p + |t| * ‖g‖) ≤ upper p := by
      apply ENNReal.ofReal_le_ofReal
      have he := herror scale hs U (ref root) root p hp
      dsimp only [upper,base]
      linarith [(abs_le.mp he).2]
    have hsub : event ⊆ {p | coord p.1 - root ∈ U} := fun p hp ↦ hp.2.2.2.2.2.2.2.2.2
    calc
      _ ≤ ∫⁻ p in event, upper p ∂Γ := setLIntegral_mono hupper hbound
      _ ≤ ∫⁻ p in {p | coord p.1 - root ∈ U}, upper p ∂Γ := lintegral_mono_set hsub
      _ = _ := by
        have hsource : MeasurableSet {p : M × M | coord p.1 - root ∈ U} :=
          hU.preimage ((hcoord.comp measurable_fst).sub measurable_const)
        rw [cavityRootWindowReadout,← lintegral_indicator hsource]
        apply lintegral_congr
        intro p
        by_cases hp : coord p.1 - root ∈ U <;> simp [hp]
  have havg := (lintegral_mono (fun root ↦
    mul_le_mul_of_nonneg_left (hpoint root) bot_le)).trans
      (lintegral_cavityRoot_scaled_window_le volume Γ _ (hcoord.comp measurable_fst)
        upper hupper U hU rootDomain N hN)
  apply havg.trans_eq
  congr 1
  have heq (p : M × M) : upper p = ENNReal.ofReal (base p) + ENNReal.ofReal ε :=
    ENNReal.ofReal_add (hb0 p) hε.le
  simp_rw [heq]
  rw [lintegral_add_left hb.ennreal_ofReal,lintegral_const]

end PopulationLocalPressureCore
end OTSelector.Reconstruction
