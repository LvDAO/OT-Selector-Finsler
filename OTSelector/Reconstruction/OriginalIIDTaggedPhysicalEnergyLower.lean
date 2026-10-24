import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicTaylor
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedCoreCarrierInclusion
import OTSelector.Reconstruction.MarkedStationaryValuePalmRootedEnergy
import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootScale

/-! Actual two-endpoint Finsler Taylor comparison in the same original
root-dependent matrix, before any conditional Palm or pressure passage. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
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

/-- The original core's actual two-endpoint remainder gives a uniform scaled
Taylor error on every bounded rooted window. The reference matrix stays at the
original macro root, and no coefficient-freezing or energy bound is assumed. -/
theorem exists_uniform_original_rooted_taylor_error
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) (R : ℝ) (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let w := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ z ∈ C.roots, ∀ x y : M,
      a x ∈ C.roots → a y ∈ C.roots →
      x ∈ F.potentialRegularDomain u → y ∈ F.potentialRegularDomain u →
      (u x,u y) ∈ C.window.region →
      ‖scale • e (w (a x)) - scale • e (w z)‖ ≤ R →
      ‖scale • e (w (a y)) - scale • e (w z)‖ ≤ R →
      |scale ^ 2 * ((F.lengthEDist x y).toReal - u y + u x) -
        matrixQuadratic (C.matrix z (u x,u y))
          (scale • (e (w (a y)) - e (w (a x))))| ≤ ε := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  intro C S w e
  let B : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hLB : ‖e.symm.toContinuousLinearMap‖ ≤ B := by dsimp [B]; linarith
  let η : ℝ := ε / ((B * R) ^ 2 + 1)
  have hden : 0 < (B * R) ^ 2 + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨radius,hradius,hrem⟩ := D.remainder η hη
  let threshold := B * R / radius + 1
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs z hz x y hx hy hxreg hyreg hp hxR hyR
  have hscale : 0 < scale := hthreshold.trans_le hs
  have hscaled (p : M) (hpR : ‖scale • e (w (a p)) - scale • e (w z)‖ ≤ R) :
      scale * ‖w (a p) - w z‖ ≤ B * R := by
    have hcoord : scale * ‖e (w (a p) - w z)‖ ≤ R := by
      rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hscale] at hpR
      simpa only [map_sub] using hpR
    have hnorm : ‖w (a p) - w z‖ ≤ B * ‖e (w (a p) - w z)‖ := by
      have hi : ‖w (a p) - w z‖ ≤
          ‖e.symm.toContinuousLinearMap‖ * ‖e (w (a p) - w z)‖ := by
        simpa using e.symm.toContinuousLinearMap.le_opNorm (e (w (a p) - w z))
      exact hi.trans (mul_le_mul_of_nonneg_right hLB (norm_nonneg _))
    nlinarith
  have hpair : scale * ‖(w (a x) - w z,w (a y) - w z)‖ ≤ B * R := by
    simp only [Prod.norm_def]
    rw [mul_max_of_nonneg _ _ hscale.le]
    exact max_le (hscaled x hxR) (hscaled y hyR)
  have hsmall : ‖(w (a x) - w z,w (a y) - w z)‖ < radius := by
    have hlt : B * R / radius < scale := by dsimp [threshold] at hs; linarith
    have hmul := (div_lt_iff₀ hradius).mp hlt
    nlinarith
  have hxlabel := C.root_label_mem_window hF hcomplete hu ha hinj hx
  have hylabel := C.root_label_mem_window hF hcomplete hu ha hinj hy
  have hxread := C.physical_readout_of_regular hF hcomplete hu ha hinj horder hxreg hx
    (C.window.region_subset hp).1
  have hyread := C.physical_readout_of_regular hF hcomplete hu ha hinj horder hyreg hy
    (C.window.region_subset hp).2.1
  have hxcurve : S.curve (w (a x)) (u x - S.level) = x :=
    (populationSeedPhysicalMap_at_label S ⟨w (a x),hxlabel.1⟩ (u x)).symm.trans hxread
  have hycurve : S.curve (w (a y)) (u y - S.level) = y :=
    (populationSeedPhysicalMap_at_label S ⟨w (a y),hylabel.1⟩ (u y)).symm.trans hyread
  have ht := hrem i z hz (u x,u y) hp (w (a x)) hxlabel (w (a y)) hylabel hsmall
  change |populationSeedPairDeficit S (u x,u y) (w (a x),w (a y)) -
    populationSeedRootQuadratic S a z (u x,u y) (w (a x) - w z,w (a y) - w z)| ≤
      η * ‖(w (a x) - w z,w (a y) - w z)‖ ^ 2 at ht
  rw [populationSeedPairDeficit,hxcurve,hycurve] at ht
  have hquad : populationSeedRootQuadratic S a z (u x,u y)
      (w (a x) - w z,w (a y) - w z) =
      matrixQuadratic (C.matrix z (u x,u y)) (e (w (a y)) - e (w (a x))) := by
    simp only [populationSeedRootQuadratic,OriginalPopulationCoefficientCore.matrix,
      sub_sub_sub_cancel_right,map_sub,e,S]
    rfl
  rw [hquad] at ht
  rw [matrixQuadratic_smul,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg scale)]
  calc
    _ ≤ scale ^ 2 * (η * ‖(w (a x) - w z,w (a y) - w z)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg scale)
    _ = η * (scale * ‖(w (a x) - w z,w (a y) - w z)‖) ^ 2 := by ring
    _ ≤ η * (B * R) ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hscale.le (norm_nonneg _)) hpair 2) hη.le
    _ ≤ ε := by
      have heq : η * ((B * R) ^ 2 + 1) = ε :=
        div_mul_cancel₀ ε (ne_of_gt hden)
      nlinarith


/-- The literal finite Taylor window retains original core labels, regular
physical endpoints, legal clocks, both rooted endpoint cutoffs, and the exact
original macro-root correspondence. Its source window is arbitrary measurable. -/
def originalRootedTaylorWindow
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (R scale : ℝ)
    (U : Set (D.coreSpatialCoordinateSpace i)) (z : ℚ → M)
    (root : D.coreSpatialCoordinateSpace i) : Set (M × M) :=
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let w := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  {p | z ∈ C.roots ∧ root = scale • e (w z) ∧
    a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧
    p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u ∧
    (u p.1,u p.2) ∈ C.window.region ∧
    ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale p.1 - root‖ ≤ R ∧
    ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale p.2 - root‖ ≤ R ∧
    physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale p.1 - root ∈ U}

/-- The full original coefficient and displacement in the same physical seed basis. -/
def originalRootedTaylorKinetic
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (scale : ℝ) (z : ℚ → M) (p : M × M) : ℝ :=
  let C := D.haar.continuous.coefficient i
  matrixQuadratic (C.matrix z (u p.1,u p.2))
    (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale p.2 -
      physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale p.1)

/-- Original geometric Taylor data give a true finite Haar-window comparison.
The same matrix is evaluated at each original reference root. Its arbitrarily
small additive error is paid by original edge mass once, with exact N/root
normalization and without any limiting-energy or pressure premise. -/
theorem exists_uniform_original_rooted_taylor_window_energy_le
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) (R : ℝ) (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ],
      ∀ (rootDomain U : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet U →
      ∀ (N : ℝ), 0 < N → ∀ ref : D.coreSpatialCoordinateSpace i → (ℚ → M),
      (∫⁻ root, ENNReal.ofReal N *
        (∫⁻ p in D.originalRootedTaylorWindow i R scale U (ref root) root,
          ENNReal.ofReal (D.originalRootedTaylorKinetic i scale (ref root) p) ∂Γ)
        ∂cavityRootMeasure volume rootDomain N) ≤
      volume U * ((∫⁻ p, ENNReal.ofReal (scale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ) + ENNReal.ofReal ε * Γ univ) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨threshold,hthreshold,htaylor⟩ :=
    D.exists_uniform_original_rooted_taylor_error hF hcomplete hu ha hinj horder i R hR hε
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs Γ _ rootDomain U hU N hN ref
  let C := D.haar.continuous.coefficient i
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale
  let base : M × M → ℝ := fun p ↦ scale ^ 2 *
    ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)
  have hb : Measurable base := (F.measurable_distance_slack hu).const_mul (scale ^ 2)
  have hb0 (p : M × M) : 0 ≤ base p := by
    have h := hu.le_add_mul p.2 p.1
    simp only [NNReal.coe_one,one_mul,dist_comm p.2 p.1] at h
    exact mul_nonneg (sq_nonneg scale) (by change 0 ≤ dist p.1 p.2 - u p.2 + u p.1; linarith)
  let upper : M × M → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (base p + ε)
  have hupper : Measurable upper := (hb.add_const ε).ennreal_ofReal
  have hcoord : Measurable coord :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ scale
  have hpoint (root : D.coreSpatialCoordinateSpace i) :
      (∫⁻ p in D.originalRootedTaylorWindow i R scale U (ref root) root,
        ENNReal.ofReal (D.originalRootedTaylorKinetic i scale (ref root) p) ∂Γ) ≤
      cavityRootWindowReadout Γ (fun p ↦ coord p.1) upper U root := by
    let event := D.originalRootedTaylorWindow i R scale U (ref root) root
    have hbound (p : M × M) (hp : p ∈ event) :
        ENNReal.ofReal (D.originalRootedTaylorKinetic i scale (ref root) p) ≤ upper p := by
      rcases hp with ⟨hz,hroot,hx,hy,hxr,hyr,hclock,hxR,hyR,hsource⟩
      have hxR' := hxR
      have hyR' := hyR
      rw [hroot] at hxR' hyR'
      have h := htaylor scale hs (ref root) hz p.1 p.2 hx hy hxr hyr hclock hxR' hyR'
      have heq : D.originalRootedTaylorKinetic i scale (ref root) p =
          matrixQuadratic (C.matrix (ref root) (u p.1,u p.2))
            (scale • ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
                (populationSeedRootLabelValue (P C.seedIndex).seed a (a p.2)) -
              (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
                (populationSeedRootLabelValue (P C.seedIndex).seed a (a p.1)))) := by
        simp only [originalRootedTaylorKinetic,physicalSceneOriginalSeedScaledPosition,
          physicalSceneOriginalSeedBasisPosition,smul_sub,C]
        rfl
      apply ENNReal.ofReal_le_ofReal
      dsimp only [upper,base]
      rw [heq]
      linarith [(abs_le.mp h).1]
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


/-- The actual growing two-product iid experiment and any measurable varying
cost retain the same optimizer in the finite geometric comparison. The canonical
spatial scale is 2*haarRootRadius(q,n+1), so the integer edge prefactor and root
normalization are both n+1. No expected Palm or pressure bound is an input. -/
theorem eventually_originalIID_canonical_tagged_taylor_energy_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count)
    (hq : 0 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) :
    let q := finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker
    let s := fun n : ℕ ↦ 2 * haarRootRadius q ((n : ℝ) + 1)
    let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := fun n ↦ originalIIDOptimalPhysicalPlan (n := n + 1) (cost n) (k n)
    ∀ᶠ n in atTop,
      ∀ (rootDomain U : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet U →
      ∀ ref : D.coreSpatialCoordinateSpace i → (ℚ → M),
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ) + 1) *
        (∫⁻ p in D.originalRootedTaylorWindow i R (s n) U (ref root) root,
          ENNReal.ofReal (D.originalRootedTaylorKinetic i (s n) (ref root) p) ∂Γ n ξ)
        ∂cavityRootMeasure volume rootDomain ((n : ℝ) + 1) ∂law n) ≤
      volume U * ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((s n) ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ n ξ ∂law n) + ENNReal.ofReal ε) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro q s law Γ
  obtain ⟨threshold,hthreshold,hbound⟩ :=
    D.exists_uniform_original_rooted_taylor_window_energy_le hF hcomplete hu ha hinj horder
      i R hR hε
  have hNlarge : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hslarge : Tendsto s atTop atTop :=
    (tendsto_haarRootRadius q hq hNlarge).const_mul_atTop (by norm_num)
  filter_upwards [hslarge.eventually (eventually_ge_atTop threshold)] with n hn
  intro rootDomain U hU ref
  let energy : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) → ℝ≥0∞ := fun ξ ↦
    ∫⁻ p, ENNReal.ofReal ((s n) ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ n ξ
  have hm : Measurable energy := (Measure.measurable_lintegral
    (((F.measurable_distance_slack hu).const_mul ((s n) ^ 2)).ennreal_ofReal)).comp
      (measurable_originalIIDOptimalPhysicalPlan (cost n) (hcost n) (k n))
  calc
    _ ≤ ∫⁻ ξ, volume U * (energy ξ + ENNReal.ofReal ε) ∂law n := by
      apply lintegral_mono
      intro ξ
      simpa only [measure_univ,mul_one] using
        hbound (s n) hn (Γ n ξ) rootDomain U hU ((n : ℝ) + 1) (by positivity) ref
    _ = _ := by
      have hmplus : Measurable (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦
          energy ξ + ENNReal.ofReal ε) := hm.add measurable_const
      rw [lintegral_const_mul _ hmplus,lintegral_add_left hm,
        lintegral_const,measure_univ,mul_one]


/-- The canonical macro rooting scale squares to the original physical energy scale. -/
theorem canonical_original_rooted_taylor_scale_sq (q n : ℕ) :
    (2 * haarRootRadius q ((n : ℝ) + 1)) ^ 2 = ((n : ℝ) + 1) ^ (2 / (q : ℝ)) := by
  have hN : 0 ≤ (n : ℝ) + 1 := by positivity
  have hs : 2 * haarRootRadius q ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ (1 / (q : ℝ)) := by
    unfold haarRootRadius
    ring
  rw [hs,← Real.rpow_mul_natCast hN]
  congr 1
  ring

/-- Recover the actual original population root from its original seed-basis macro coordinate. -/
def originalRootedTaylorReference
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (c : D.coreSpatialCoordinateSpace i) : ℚ → M :=
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  a (S.curve ((Module.finBasis ℝ S.covector.ker).equivFunL.symm c) 0)

/-- On the measured original coordinate core this is the literal original root,
so the Taylor reference map agrees with the fixed-root Poisson input reference. -/
theorem originalRootedTaylorReference_coreMacroLabel
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {z : ℚ → M}
    (hz : z ∈ (D.haar.continuous.coefficient i).roots) :
    D.originalRootedTaylorReference i (D.coreMacroLabel i z) = z := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  have hroot := (fixed_seed_rootLabel_recovery hF hcomplete hu ha hinj
    (D.haar.continuous.coefficient i).seedIndex
    ((D.haar.continuous.coefficient i).roots_subset_piece hz)).2
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  change a (S.curve (e.symm (e (populationSeedRootLabelValue S a z))) 0) = z
  rw [e.symm_apply_apply]
  exact hroot

/-- The actual inverse seed reference has the exact normalized root relation
on the whole measured coordinate core, without any boundary-null premise. -/
theorem originalRootedTaylorReference_normalized_root
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {scale : ℝ} (hscale : scale ≠ 0)
    (root : D.coreSpatialCoordinateSpace i)
    (hroot : scale⁻¹ • root ∈ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots) :
    let z := D.originalRootedTaylorReference i (scale⁻¹ • root)
    z ∈ (D.haar.continuous.coefficient i).roots ∧ root = scale • D.coreMacroLabel i z := by
  obtain ⟨z,hz,heq⟩ := hroot
  have href : D.originalRootedTaylorReference i (scale⁻¹ • root) = z := by
    rw [← heq]
    exact D.originalRootedTaylorReference_coreMacroLabel hF hcomplete hu ha hinj i hz
  dsimp only
  rw [href]
  refine ⟨hz,?_⟩
  rw [heq,smul_smul,mul_inv_cancel₀ hscale,one_smul]

/-- The literal Taylor window already lies inside the same original fixed seed
source mask. Thus using the original source-restricted optimizer changes no edge
of this finite geometric readout. -/
theorem originalRootedTaylorWindow_sourceRestriction
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (R scale : ℝ)
    (U : Set (D.coreSpatialCoordinateSpace i)) (z : ℚ → M)
    (root : D.coreSpatialCoordinateSpace i) (Γ : Measure (M × M)) :
    (Γ.restrict (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex ×ˢ (univ : Set M))).restrict
      (D.originalRootedTaylorWindow i R scale U z root) =
      Γ.restrict (D.originalRootedTaylorWindow i R scale U z root) := by
  apply Measure.restrict_restrict_of_subset
  intro p hp
  exact ⟨(D.haar.continuous.coefficient i).roots_subset_piece hp.2.2.1,mem_univ _⟩

end PopulationLocalPressureCore
end OTSelector.Reconstruction
