import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicLabelGeometry
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopic
import OTSelector.Reconstruction.FinslerCoefficientCoreLocalPressure
import OTSelector.Geometry.FinslerDistanceLocalizationCompact

/-!
# The actual original scaled slack near its original macroscopic label

An actual Taylor cover selects its own frozen coefficient center, which need
not equal the macroscopic center. Compact inverse-label continuity sends both
actual roots into that selected neighborhood. Exact physical readout then
identifies the original slack, and quadratic homogeneity gives the comparison
in the actual rooted displacement at the original spatial scale.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- The actual macro tag root/scale is exactly inverse scaling in the original
seed basis, including the zero-scale fallback of the original definition. -/
theorem physicalSceneMacroscopicRoot_eq_inv_smul
    {ι : Type*} (scale : ℝ) (root : ι → ℝ) :
    physicalSceneMacroscopicRoot scale root = scale⁻¹ • root := by
  ext i
  simp only [physicalSceneMacroscopicRoot, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
    mul_comm]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- The literal original scaled slack is compared to the original matrix at
one frozen root and the actual clock pair, evaluated on the actual rooted
seed-basis displacement. This predicate is an output of the certificate. -/
def ActualScaledTaylorBound (ε : ℝ) (frozenRoot : ℚ → M)
    (scale : ℝ) (root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    (x y : M) : Prop :=
  let Δ :=
    (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale y - root) -
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale x - root)
  |scale ^ 2 * ((F.lengthEDist x y).toReal - u y + u x) -
      matrixQuadratic (C.matrix frozenRoot (u x, u y)) Δ| ≤
    (2 * ε) * matrixQuadratic (C.matrix frozenRoot (u x, u y)) Δ

/-- An actual macroscopic label neighborhood and its internally selected
Taylor center. The frozen center belongs to the Taylor cover and may differ
from the original macroscopic center. -/
structure ActualMacroscopicTaylorCertificate {ε : ℝ} (T : C.TaylorRootCover ε)
    (K : Set (ℚ → M)) (macroCenter : ℚ → M) where
  frozenCenter : ℚ → M
  frozenCenter_mem : frozenCenter ∈ T.centers
  macroCenter_mem_neighborhood : macroCenter ∈ T.neighborhood frozenCenter
  macroRadius : ℝ
  macroRadius_pos : 0 < macroRadius
  relative_bound : ∀ scale : ℝ, 0 < scale →
    ∀ root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ, ∀ R : ℝ,
      dist (physicalSceneMacroscopicRoot scale root)
        ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
          (populationSeedRootLabelValue (P C.seedIndex).seed a macroCenter)) < macroRadius →
      R / scale < macroRadius → ∀ x y : M, a x ∈ K → a y ∈ K →
      ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale x - root‖ ≤ R →
      ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale y - root‖ ≤ R →
      (u x, u y) ∈ C.window.region →
      populationSeedPhysicalMap (P C.seedIndex).seed
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a x), u x) = x →
      populationSeedPhysicalMap (P C.seedIndex).seed
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a y), u y) = y →
      C.ActualScaledTaylorBound ε frozenCenter scale root x y

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Original regularity, the actual root, and its retained clock interval give
the exact physical seed readout, using the original label-clock injectivity. -/
theorem physical_readout_of_regular
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {x : M} (hxreg : x ∈ F.potentialRegularDomain u) (hx : a x ∈ C.roots)
    (ht : u x ∈ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ)) :
    populationSeedPhysicalMap (P C.seedIndex).seed
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a x), u x) = x := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let S := (P C.seedIndex).seed
  let w := populationSeedRootLabelValue S a (a x)
  obtain ⟨hw, hroot⟩ := fixed_seed_rootLabel_recovery hF hcomplete hu ha hinj
    C.seedIndex (C.roots_subset_piece hx)
  have htime : u x - S.level ∈ interior (S.calibrationTimes w) :=
    C.calibrated_label_interval hF hcomplete hu ha hinj hx
      ⟨sub_le_sub_right ht.1 _, sub_le_sub_right ht.2 _⟩
  obtain ⟨hreg, hlabel⟩ := S.active_point_root_data hF hcomplete hu horder hw htime
  have hclock : u (S.curve w (u x - S.level)) = u x := by
    have hc := interior_subset htime
    change u (S.curve w (u x - S.level)) = (S.level : ℝ) + (u x - S.level) at hc
    simpa only [add_sub_cancel] using hc
  have heq : S.curve w (u x - S.level) = x := by
    exact congrArg Subtype.val (hinj (Prod.ext (hlabel.trans hroot) hclock) :
      (⟨S.curve w (u x - S.level), hreg⟩ : F.potentialRegularDomain u) = ⟨x, hxreg⟩)
  exact (populationSeedPhysicalMap_at_label S ⟨w, hw⟩ (u x)).trans heq

/-- Exact physical reconstruction identifies the same original slack with the
Taylor comparison. Homogeneity moves the same coefficient to the actual rooted
displacement, with no change of matrix or scalar clocks. -/
theorem TaylorRootCover.actual_scaled_relative_distance
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (T : C.TaylorRootCover ε) (hε : 0 ≤ ε) {c : ℚ → M} (hc : c ∈ T.centers)
    {x y : M} (hx : a x ∈ C.roots ∩ T.neighborhood c)
    (hy : a y ∈ C.roots ∩ T.neighborhood c) (hp : (u x, u y) ∈ C.window.region)
    (hxread : populationSeedPhysicalMap (P C.seedIndex).seed
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a x), u x) = x)
    (hyread : populationSeedPhysicalMap (P C.seedIndex).seed
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a y), u y) = y)
    (scale : ℝ) (root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) :
    C.ActualScaledTaylorBound ε c scale root x y := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let S := (P C.seedIndex).seed
  let w := populationSeedRootLabelValue S a
  let bW := Module.finBasis ℝ S.covector.ker
  let v := bW.equivFun (w (a y) - w (a x))
  have hxlabel := C.root_label_mem_window hF hcomplete hu ha hinj hx.1
  have hylabel := C.root_label_mem_window hF hcomplete hu ha hinj hy.1
  have hxcurve : S.curve (w (a x)) (u x - S.level) = x :=
    (populationSeedPhysicalMap_at_label S ⟨w (a x), hxlabel.1⟩ (u x)).symm.trans hxread
  have hycurve : S.curve (w (a y)) (u y - S.level) = y :=
    (populationSeedPhysicalMap_at_label S ⟨w (a y), hylabel.1⟩ (u y)).symm.trans hyread
  have hb := T.relative_distance hF hcomplete hu ha hinj hε hc hx hy hp
  change |populationSeedPairDeficit S (u x, u y) (w (a x), w (a y)) -
    matrixQuadratic (C.matrix c (u x, u y)) v| ≤
      (2 * ε) * matrixQuadratic (C.matrix c (u x, u y)) v at hb
  rw [populationSeedPairDeficit, hxcurve, hycurve] at hb
  have hd :
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale y - root) -
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale x - root) =
      scale • v := by
    simp only [physicalSceneOriginalSeedScaledPosition, physicalSceneOriginalSeedBasisPosition,
      sub_sub_sub_cancel_right, v, w, bW, S, map_sub, smul_sub]
  unfold ActualScaledTaylorBound
  dsimp only
  rw [hd, matrixQuadratic_smul]
  calc
    |scale ^ 2 * ((F.lengthEDist x y).toReal - u y + u x) -
        scale ^ 2 * matrixQuadratic (C.matrix c (u x, u y)) v| =
        scale ^ 2 * |((F.lengthEDist x y).toReal - u y + u x) -
          matrixQuadratic (C.matrix c (u x, u y)) v| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg scale)]
    _ ≤ scale ^ 2 * ((2 * ε) * matrixQuadratic (C.matrix c (u x, u y)) v) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg scale)
    _ = _ := by ring

/-- Every macroscopic center in the compact original label core selects one
actual Taylor center and a positive macro radius before scale and endpoints. -/
theorem TaylorRootCover.nonempty_actualMacroscopicTaylorCertificate
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (T : C.TaylorRootCover ε) (hε : 0 ≤ ε)
    {K : Set (ℚ → M)} (hK : IsCompact K) (hsub : K ⊆ C.roots)
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) K)
    {macroCenter : ℚ → M} (hmacroCenter : macroCenter ∈ K) :
    Nonempty (C.ActualMacroscopicTaylorCertificate T K macroCenter) := by
  obtain ⟨c, hc, hcenterU⟩ := mem_iUnion₂.mp (T.covers (hsub hmacroCenter))
  obtain ⟨radius, hradius, hmem⟩ :=
    exists_fixed_seed_macro_rooted_window_into_root_neighborhood hF hcomplete hu ha hinj
      C.seedIndex hK (hsub.trans C.roots_subset_piece) hlabel
      (T.open_neighborhood c hc) hmacroCenter hcenterU
  refine ⟨{
    frozenCenter := c
    frozenCenter_mem := hc
    macroCenter_mem_neighborhood := hcenterU
    macroRadius := radius
    macroRadius_pos := hradius
    relative_bound := ?_ }⟩
  intro scale hscale root R hmacro hsmall x y hx hy hxR hyR hp hxread hyread
  obtain ⟨hxU, hyU⟩ := hmem scale hscale root R
    (by simpa only [physicalSceneMacroscopicRoot_eq_inv_smul] using hmacro)
    hsmall x y hx hy hxR hyR
  exact T.actual_scaled_relative_distance hF hcomplete hu ha hinj hε hc
    ⟨hsub hxU.1, hxU.2⟩ ⟨hsub hyU.1, hyU.2⟩ hp hxread hyread scale root

/-- The cover and its macroscopic certificate are produced from the original
coefficient, continuous original labels, and actual source remainder. -/
theorem exists_actualMacroscopicTaylorCertificate
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots)
    (hrem : ∀ η > 0, ∃ radius > 0,
      ∀ z ∈ C.roots, C.SourceCoordinateRemainderBound z η radius)
    {ε : ℝ} (hε : 0 < ε) {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ C.roots) {macroCenter : ℚ → M} (hmacroCenter : macroCenter ∈ K) :
    ∃ T : C.TaylorRootCover ε,
      Nonempty (C.ActualMacroscopicTaylorCertificate T K macroCenter) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨T⟩ := C.exists_taylorRootCover hlabel hrem hε
  exact ⟨T, T.nonempty_actualMacroscopicTaylorCertificate hF hcomplete hu ha hinj hε.le
    hK hsub (hlabel.mono hsub) hmacroCenter⟩

/-- Original regular endpoints provide the exact physical readout required by
the certificate; no approximation of the original cost is an input. -/
theorem ActualMacroscopicTaylorCertificate.relative_bound_of_regular
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {T : C.TaylorRootCover ε} {K : Set (ℚ → M)} {macroCenter : ℚ → M}
    (A : C.ActualMacroscopicTaylorCertificate T K macroCenter) (hsub : K ⊆ C.roots)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (scale : ℝ) (hscale : 0 < scale)
    (root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (R : ℝ)
    (hmacro : dist (physicalSceneMacroscopicRoot scale root)
      ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
        (populationSeedRootLabelValue (P C.seedIndex).seed a macroCenter)) < A.macroRadius)
    (hsmall : R / scale < A.macroRadius)
    {x y : M} (hx : a x ∈ K) (hy : a y ∈ K)
    (hxR : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale x - root‖ ≤ R)
    (hyR : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale y - root‖ ≤ R)
    (hp : (u x, u y) ∈ C.window.region)
    (hxreg : x ∈ F.potentialRegularDomain u) (hyreg : y ∈ F.potentialRegularDomain u) :
    C.ActualScaledTaylorBound ε A.frozenCenter scale root x y := by
  have ht := C.window.region_subset hp
  exact A.relative_bound scale hscale root R hmacro hsmall x y hx hy hxR hyR hp
    (C.physical_readout_of_regular hF hcomplete hu ha hinj horder hxreg (hsub hx) ht.1)
    (C.physical_readout_of_regular hF hcomplete hu ha hinj horder hyreg (hsub hy) ht.2.1)

/-- For every fixed actual rooted window radius, one explicit positive scale
threshold ensures the certificate on all larger original spatial scales. -/
theorem ActualMacroscopicTaylorCertificate.exists_scale_threshold_of_regular
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {T : C.TaylorRootCover ε} {K : Set (ℚ → M)} {macroCenter : ℚ → M}
    (A : C.ActualMacroscopicTaylorCertificate T K macroCenter) (hsub : K ⊆ C.roots)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (R : ℝ) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
      dist (physicalSceneMacroscopicRoot scale root)
        ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
          (populationSeedRootLabelValue (P C.seedIndex).seed a macroCenter)) < A.macroRadius →
      ∀ x y : M, a x ∈ K → a y ∈ K →
      ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale x - root‖ ≤ R →
      ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale y - root‖ ≤ R →
      (u x, u y) ∈ C.window.region →
      x ∈ F.potentialRegularDomain u → y ∈ F.potentialRegularDomain u →
      C.ActualScaledTaylorBound ε A.frozenCenter scale root x y := by
  let threshold := (|R| + 1) / A.macroRadius + 1
  have hRadius := A.macroRadius_pos
  have hthreshold : 0 < threshold := by
    dsimp only [threshold]
    positivity
  refine ⟨threshold, hthreshold, ?_⟩
  intro scale hs root hmacro x y hx hy hxR hyR hp hxreg hyreg
  have hscale : 0 < scale := hthreshold.trans_le hs
  have hsmall : R / scale < A.macroRadius := by
    apply (div_lt_iff₀ hscale).mpr
    have hlt : (|R| + 1) / A.macroRadius < scale := by
      dsimp only [threshold] at hs
      linarith
    have hprod := (div_lt_iff₀ A.macroRadius_pos).mp hlt
    nlinarith [le_abs_self R]
  exact A.relative_bound_of_regular hF hcomplete hu ha hinj hsub horder
    scale hscale root R hmacro hsmall hx hy hxR hyR hp hxreg hyreg

omit hF hcomplete hu ha hinj in
/-- The relative error certificate also gives the explicit upper and lower
comparison with the very same original frozen quadratic form. -/
theorem ActualScaledTaylorBound.two_sided
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {frozenRoot : ℚ → M} {scale : ℝ}
    {root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ} {x y : M}
    (h : C.ActualScaledTaylorBound ε frozenRoot scale root x y) :
    let Δ :=
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale y - root) -
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale x - root)
    let Q := matrixQuadratic (C.matrix frozenRoot (u x, u y)) Δ
    (1 - 2 * ε) * Q ≤ scale ^ 2 * ((F.lengthEDist x y).toReal - u y + u x) ∧
      scale ^ 2 * ((F.lengthEDist x y).toReal - u y + u x) ≤ (1 + 2 * ε) * Q := by
  dsimp only [ActualScaledTaylorBound] at h
  dsimp only
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> nlinarith

end OriginalPopulationCoefficientCore

variable {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {loss : ℝ≥0∞}

/-- The original local pressure core internally supplies the continuous label
and geometric remainder used to produce an actual macroscopic Taylor certificate. -/
theorem PopulationLocalPressureCore.exists_actualMacroscopicTaylorCertificate
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {ε : ℝ} (hε : 0 < ε)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ (D.haar.continuous.coefficient i).roots)
    {macroCenter : ℚ → M} (hmacroCenter : macroCenter ∈ K) :
    ∃ T : (D.haar.continuous.coefficient i).TaylorRootCover ε,
      Nonempty ((D.haar.continuous.coefficient i).ActualMacroscopicTaylorCertificate
        T K macroCenter) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  have hlabel : ContinuousOn
      (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots := by
    rw [← D.haar.intensity_roots i]
    exact (D.haar.intensity i).continuous_label
  exact C.exists_actualMacroscopicTaylorCertificate hF hcomplete hu ha hinj hlabel
    (D.source_remainder_on_piece hF hcomplete hu ha hinj i) hε hK hsub hmacroCenter

end OTSelector.Reconstruction
