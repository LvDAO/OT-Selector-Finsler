import OTSelector.Reconstruction.OriginalIIDLocalIntensity
import OTSelector.Reconstruction.OriginalIIDLocalCellOscillation
import OTSelector.Reconstruction.OriginalIIDFrozenMaskedLaplace
import OTSelector.Probability.IIDLaplaceLimit
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local Laplace limits from the original population geometry

The full original iid laws are retained. Compact-core continuity controls raw
conditional laws, density-point estimates remove mask boundaries, and exact
native Haar normalization identifies both colors on one common root set.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Metric Module Manifold OTSelector.Geometry
open scoped Topology ENNReal NNReal ContDiff BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- A test supported in a smaller measurable cell has the same original
restricted integral in the smaller and larger cells. -/
theorem original_setIntegral_localize
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {A B : Set X}
    (hA : MeasurableSet A) (hsub : B ⊆ A) {f : X → ℝ}
    (hzero : ∀ x ∈ A \ B, f x = 0) :
    (∫ x in A, f x ∂μ) = ∫ x in B, f x ∂μ :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA hsub hzero

/-- Restricted native Haar-clock integrals use the SAME finite basis and
retain its exact coordinate-volume factor. -/
theorem original_integral_restrict_haar_product_coordinates
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {q : ℕ}
    (κ : Measure V) [κ.IsAddHaarMeasure] (e : V ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    (A : Set V) (α : Measure ℝ) [SFinite α]
    (f : (Fin q → ℝ) × ℝ → ℝ) (hf : Measurable f) :
    (∫ p : V × ℝ, f (e p.1, p.2) ∂(κ.restrict A).prod α) =
      c.toReal * ∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ e '' A}, f p
        ∂((volume : Measure (Fin q → ℝ)).prod α) := by
  have hrestricted : (κ.restrict A).map e =
      c • (volume : Measure (Fin q → ℝ)).restrict (e '' A) := by
    calc
      _ = (κ.map e).restrict (e '' A) := by
        have he := e.toHomeomorph.measurableEmbedding.restrict_map κ (e '' A)
        change (κ.map e).restrict (e '' A) = (κ.restrict (e ⁻¹' (e '' A))).map e at he
        simpa only [preimage_image_eq _ e.injective] using he.symm
      _ = _ := by rw [hmap, Measure.restrict_smul]
  have hprod : ((κ.restrict A).prod α).map (Prod.map e id) =
      (c • (volume : Measure (Fin q → ℝ)).restrict (e '' A)).prod α := by
    rw [← Measure.map_prod_map _ _ e.continuous.measurable measurable_id,
      Measure.map_id, hrestricted]
  have hobs : Measurable (Prod.map e (id : ℝ → ℝ)) :=
    e.continuous.measurable.prodMap measurable_id
  have hi := integral_map (μ := (κ.restrict A).prod α) (f := f)
    hobs.aemeasurable hf.aestronglyMeasurable
  rw [hprod, Measure.prod_smul_left, integral_smul_measure,
    Measure.restrict_prod_eq_prod_univ] at hi
  have hset : (e '' A) ×ˢ (univ : Set ℝ) =
      {p : (Fin q → ℝ) × ℝ | p.1 ∈ e '' A} := by ext p; simp
  rw [hset] at hi
  change c.toReal • (∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ e '' A}, f p
    ∂((volume : Measure (Fin q → ℝ)).prod α)) =
      ∫ p : V × ℝ, f (e p.1, p.2) ∂(κ.restrict A).prod α at hi
  simpa only [smul_eq_mul] using hi.symm

/-- An arbitrary-tolerance normalized raw-law error bound forces the test
error to vanish. The bound is later supplied by actual compact-core continuity. -/
theorem original_tendsto_zero_of_eventually_le_tolerance
    {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, |f n| ≤ C * ε) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h (ε / (C + 1)) (div_pos hε (by linarith)))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hc : C * (ε / (C + 1)) < ε := by
    have he : ε / (C + 1) > 0 := div_pos hε (by linarith)
    have hid : (C + 1) * (ε / (C + 1)) = ε :=
      mul_div_cancel₀ ε (by linarith : C + 1 ≠ 0)
    nlinarith
  exact (hN n hn).trans_lt hc

section ActualCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual original physical cell and its frozen native-Haar endpoint law
have vanishing scaled Laplace difference at every retained reference root.
The density and clock oscillations are derived from the actual compact core;
no raw-TV convergence or test-limit callback is assumed. -/
theorem PopulationLocalPressureCore.original_scaled_cell_laplace_freezing_error_tendsto_zero
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    {ref : ℚ → M} (href : ref ∈ (D.haar.continuous.coefficient i).roots)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (H : (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ) × ℝ → ℝ)
    (hH : Measurable H) (hH0 : ∀ p, 0 ≤ H p)
    {B : ℝ} (hB : 0 < B)
    (hsupport : ∀ p, p.1 ∉ closedBall 0 B → H p = 0) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    ∀ color : Fin 2,
      let η := if color = 0 then η₀ else η₁
      let α := populationTwoColorClockKernel u a η₀ η₁ color ref
      Tendsto (fun n ↦ s n ^ q *
        ((∫ x in a ⁻¹' C.roots,
          1 - Real.exp (-H (s n • (e (R (a x)) - e (R ref)), u x)) ∂η) -
        (∫ p : S.covector.ker × ℝ,
          1 - Real.exp (-H (s n • (e p.1 - e (R ref)), p.2))
          ∂((D.rootIntensity i ref).toNNReal •
            ((κ C.seedIndex).restrict (R '' C.roots)).prod α)))) atTop (𝓝 0) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let q := finrank ℝ S.covector.ker
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let L : ℕ → Set (ℚ → M) := fun n ↦ C.roots ∩ {z | ‖e (R z - R ref)‖ ≤ B / s n}
  let Hn : ℕ → S.covector.ker × ℝ → ℝ :=
    fun n p ↦ H (s n • (e p.1 - e (R ref)), p.2)
  have hC : MeasurableSet C.roots := C.roots_compact.measurableSet
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hL n : MeasurableSet (L n) := by
    apply hC.inter
    apply measurableSet_le _ measurable_const
    fun_prop
  have hsub n : L n ⊆ C.roots := inter_subset_left
  have hHn n : Measurable (Hn n) := by apply hH.comp; fun_prop
  have hHn0 n p : 0 ≤ Hn n p := hH0 _
  have hzero n (w : S.covector.ker) (t : ℝ)
      (hw : ¬ ‖e (w - R ref)‖ ≤ B / s n) :
      1 - Real.exp (-Hn n (w, t)) = 0 := by
    have hout : s n • (e w - e (R ref)) ∉ closedBall 0 B := by
      intro hscaled
      apply hw
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hs n), ← map_sub] at hscaled
      exact (le_div_iff₀ (hs n)).mpr (by nlinarith)
    simp only [Hn, hsupport (s n • (e w - e (R ref)), t) hout, neg_zero,
      Real.exp_zero, sub_self]
  have hphys n {η : Measure M} :
      (∫ x in a ⁻¹' C.roots, 1 - Real.exp (-Hn n (R (a x), u x)) ∂η) =
        ∫ x in a ⁻¹' L n, 1 - Real.exp (-Hn n (R (a x), u x)) ∂η := by
    apply original_setIntegral_localize η (hC.preimage ha) (preimage_mono (hsub n))
    intro x hx
    apply hzero
    intro hw
    exact hx.2 ⟨hx.1, hw⟩
  have hnative n (α : Measure ℝ) [SFinite α] :
      (∫ p : S.covector.ker × ℝ, 1 - Real.exp (-Hn n p)
        ∂((D.rootIntensity i ref).toNNReal •
          ((κ C.seedIndex).restrict (R '' C.roots)).prod α)) =
      ∫ p : S.covector.ker × ℝ, 1 - Real.exp (-Hn n p)
        ∂((D.rootIntensity i ref).toNNReal •
          ((κ C.seedIndex).restrict (R '' L n)).prod α) := by
    rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    congr 1
    rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_prod_eq_prod_univ]
    apply original_setIntegral_localize _
      ((D.haar.measurable_cell_label_image hcomplete i hC Subset.rfl).prod MeasurableSet.univ)
      (Set.prod_mono (image_mono (hsub n)) Subset.rfl)
    intro p hp
    obtain ⟨z, hz, hzp⟩ := hp.1.1
    apply hzero
    intro hw
    apply hp.2
    refine ⟨?_, mem_univ _⟩
    refine ⟨z, ⟨hz, ?_⟩, hzp⟩
    change ‖e (R z - R ref)‖ ≤ B / s n
    have heq : R z = p.1 := hzp
    exact heq.symm ▸ hw
  let bound := (originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
    (volume : Measure (Fin q → ℝ)).real (closedBall 0 B)
  have hbound n : s n ^ q * (κ C.seedIndex).real (R '' L n) ≤ bound := by
    apply original_shrinking_seed_ball_haar_volume_real_le S (κ C.seedIndex) (R ref) (hs n) B
    rintro w ⟨z, hz, rfl⟩
    exact hz.2
  have hρ : 0 ≤ D.rootIntensity i ref := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ bound := mul_nonneg (NNReal.coe_nonneg _) measureReal_nonneg
  intro color
  let η : Measure M := if color = 0 then η₀ else η₁
  let α := populationTwoColorClockKernel u a η₀ η₁ color ref
  apply original_tendsto_zero_of_eventually_le_tolerance
    (C := 2 * D.rootIntensity i ref * bound) (by positivity)
  intro ε hε
  filter_upwards [D.original_cell_intensity_clock_oscillation i href s hs hlarge B hB ε hε]
    with n hn
  have hclose : ∀ z ∈ L n, |D.rootIntensity i z - D.rootIntensity i ref| ≤
      ε * D.rootIntensity i ref := fun z hz ↦ (hn z hz.1 hz.2).1
  have hmark : ∀ z ∈ L n, ∀ color : Fin 2,
      ((populationTwoColorClockKernel u a η₀ η₁ color z).toSignedMeasure -
        (populationTwoColorClockKernel u a η₀ η₁ color ref).toSignedMeasure).totalVariation
          univ ≤ ENNReal.ofReal ε := fun z hz ↦ (hn z hz.1 hz.2).2
  have hb := D.original_cell_laplace_defect_freezing_le hF hcomplete hu ha hinj i
    (hL n) (hsub n) href hε.le hclose hmark (Hn n) (hHn n) (hHn0 n) color
  have hj := D.original_cell_laplace_defect_identities hF hcomplete hu ha hinj i
    (hL n) (hsub n) (Hn n) (hHn n)
  have hactual : (∫ x in a ⁻¹' L n, 1 - Real.exp (-Hn n (R (a x), u x)) ∂η) =
      ∫ p, 1 - Real.exp (-Hn n p)
        ∂((((κ C.seedIndex).restrict (R '' L n)).withDensity
          (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)) ⊗ₘ
          populationSeedCoordinateClockKernel S a ha (populationTwoColorClockKernel u a η₀ η₁ color)) := by
    by_cases hc : color = 0
    · simpa only [η, hc, ite_true, populationTwoColorClockKernel] using hj.1
    · simpa only [η, hc, ite_false, populationTwoColorClockKernel] using hj.2
  change |s n ^ q * ((∫ x in a ⁻¹' C.roots,
      1 - Real.exp (-Hn n (R (a x), u x)) ∂η) -
    (∫ p, 1 - Real.exp (-Hn n p) ∂((D.rootIntensity i ref).toNNReal •
      ((κ C.seedIndex).restrict (R '' C.roots)).prod α)))| ≤ _
  rw [hphys n, hnative n α, hactual, abs_mul, abs_of_nonneg (pow_nonneg (hs n).le q)]
  calc
    _ ≤ s n ^ q * ((2 * ε * D.rootIntensity i ref) * (κ C.seedIndex).real (R '' L n)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg (hs n).le q)
    _ = (2 * D.rootIntensity i ref * ε) * (s n ^ q * (κ C.seedIndex).real (R '' L n)) := by ring
    _ ≤ (2 * D.rootIntensity i ref * ε) * bound :=
      mul_le_mul_of_nonneg_left (hbound n) (by positivity)
    _ = _ := by ring

/-- At a retained original root which is a coordinate density point, the actual
original iid endpoint populations have the full scaled one-point Laplace defect.
The physical cell is the original root restriction, and the limiting intensity
includes the native-Haar basis Jacobian. -/
theorem PopulationLocalPressureCore.original_scaled_cell_laplace_tendsto_at
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    {ref : ℚ → M} (href : ref ∈ (D.haar.continuous.coefficient i).roots)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (H : (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ) × ℝ → ℝ)
    (hH : Measurable H) (hH0 : ∀ p, 0 ≤ H p)
    {B : ℝ} (hB : 0 < B)
    (hsupport : ∀ p, p.1 ∉ closedBall 0 B → H p = 0)
    (hmask :
      let C := D.haar.continuous.coefficient i
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let e := (Module.finBasis ℝ S.covector.ker).equivFunL
      Tendsto (fun n ↦ s n ^ finrank ℝ S.covector.ker *
        (volume (closedBall (e (R ref)) (B / s n) \ (e '' (R '' C.roots)))).toReal)
        atTop (𝓝 0)) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    ∀ color : Fin 2,
      let η := if color = 0 then η₀ else η₁
      let α := populationTwoColorClockKernel u a η₀ η₁ color ref
      Tendsto (fun n ↦ s n ^ finrank ℝ S.covector.ker *
        ∫ x in a ⁻¹' C.roots,
          1 - Real.exp (-H (s n • (e (R (a x)) - e (R ref)), u x)) ∂η) atTop
        (𝓝 (originalSeedCoordinateIntensity P a κ lambda C.seedIndex ref *
          ∫ p, 1 - Real.exp (-H p) ∂((volume : Measure
            (Fin (finrank ℝ S.covector.ker) → ℝ)).prod α))) := by
  dsimp only at hmask ⊢
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let q := finrank ℝ S.covector.ker
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let K := e '' (R '' C.roots)
  let Θ := originalSeedCoordinateIntensity P a κ lambda C.seedIndex ref
  have hC : MeasurableSet C.roots := C.roots_compact.measurableSet
  have hA : MeasurableSet (R '' C.roots) :=
    D.haar.measurable_cell_label_image hcomplete i hC Subset.rfl
  have hK : MeasurableSet K := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hA
  have hρ : 0 ≤ D.rootIntensity i ref := ENNReal.toReal_nonneg
  have hθ : Θ = (originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ) *
      D.rootIntensity i ref := rfl
  have herr := D.original_scaled_cell_laplace_freezing_error_tendsto_zero
    hF hcomplete hu ha hinj i href s hs hlarge H hH hH0 hB hsupport
  intro color
  let α := populationTwoColorClockKernel u a η₀ η₁ color ref
  let η : Measure M := if color = 0 then η₀ else η₁
  let μ := (volume : Measure (Fin q → ℝ)).prod α
  let f : ℕ → (Fin q → ℝ) × ℝ → ℝ :=
    fun n p ↦ 1 - Real.exp (-H (s n • (p.1 - e (R ref)), p.2))
  have hf n : Measurable (f n) := by
    apply measurable_const.sub
    apply Measurable.exp
    apply Measurable.neg
    apply hH.comp
    fun_prop
  have hfrozen := (original_tendsto_scaled_masked_frozen_laplace_defect_at
    hK s hs α H hH hH0 hsupport (e (R ref)) hmask).const_mul Θ
  have heq n :
      s n ^ q * (∫ p : S.covector.ker × ℝ,
        1 - Real.exp (-H (s n • (e p.1 - e (R ref)), p.2))
        ∂((D.rootIntensity i ref).toNNReal •
          ((κ C.seedIndex).restrict (R '' C.roots)).prod α)) =
      Θ * (s n ^ q * ∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ K}, f n p ∂μ) := by
    have hid := original_integral_restrict_haar_product_coordinates (κ C.seedIndex) e
      (map_originalSeedHaar_eq_coordinate_volume S (κ C.seedIndex)) (R '' C.roots) α
      (f n) (hf n)
    change (∫ p : S.covector.ker × ℝ,
      1 - Real.exp (-H (s n • (e p.1 - e (R ref)), p.2))
        ∂((κ C.seedIndex).restrict (R '' C.roots)).prod α) =
      (originalSeedCoordinateHaarFactor S (κ C.seedIndex) : ℝ≥0∞).toReal *
        ∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ K}, f n p ∂μ at hid
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hid,
      Real.coe_toNNReal _ hρ, ENNReal.coe_toReal, hθ]
    ring
  have hfreeze : Tendsto (fun n ↦
      s n ^ q * (∫ p : S.covector.ker × ℝ,
        1 - Real.exp (-H (s n • (e p.1 - e (R ref)), p.2))
        ∂((D.rootIntensity i ref).toNNReal •
          ((κ C.seedIndex).restrict (R '' C.roots)).prod α))) atTop
      (𝓝 (Θ * ∫ p, 1 - Real.exp (-H p) ∂μ)) := by
    exact hfrozen.congr' (Eventually.of_forall fun n ↦ (heq n).symm)
  have hsum := (herr color).add hfreeze
  simp only [zero_add] at hsum
  apply hsum.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  ring

/-- ONE full-measure set of retained coordinate roots supports both original
iid colors and EVERY nonnegative measurable compact-spatial Laplace test.
The original conditional clocks are frozen separately at the recovered root;
all intensity/kernel oscillations and microscopic boundary losses are proved
from the actual core. There is no local-limit or TV-convergence hypothesis. -/
theorem PopulationLocalPressureCore.original_ae_scaled_cell_laplace_tendsto
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ (H : (Fin q → ℝ) × ℝ → ℝ), Measurable H → (∀ p, 0 ≤ H p) →
        (∃ B : ℝ, 0 < B ∧ ∀ p, p.1 ∉ closedBall 0 B → H p = 0) →
      ∀ color : Fin 2,
        let η := if color = 0 then η₀ else η₁
        let α := populationTwoColorClockKernel u a η₀ η₁ color (ref c)
        Tendsto (fun n ↦ s n ^ q *
          ∫ x in a ⁻¹' C.roots,
            1 - Real.exp (-H (s n • (e (R (a x)) - c), u x)) ∂η) atTop
          (𝓝 (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c) *
            ∫ p, 1 - Real.exp (-H p)
              ∂((volume : Measure (Fin q → ℝ)).prod α))) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let q := finrank ℝ S.covector.ker
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let K := e '' (R '' C.roots)
  let ref := fun c ↦ a (S.curve (e.symm c) 0)
  have hC : MeasurableSet C.roots := C.roots_compact.measurableSet
  have hA : MeasurableSet (R '' C.roots) :=
    D.haar.measurable_cell_label_image hcomplete i hC Subset.rfl
  have hK : MeasurableSet K := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hA
  have hmaskall : ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ k : ℕ, Tendsto (fun n ↦ s n ^ q *
        (volume (closedBall c (((k : ℝ) + 1) / s n) \ K)).toReal) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro k
    exact OTSelector.Probability.ae_tendsto_scaled_missing_volume hK s hs hlarge (by positivity)
  have hrecover (z) (hz : z ∈ C.roots) : ref (e (R z)) = z := by
    dsimp only [ref]
    rw [e.symm_apply_apply]
    exact (D.haar.intensity i).root_identity z ((D.haar.intensity_roots i).symm ▸ hz)
  filter_upwards [ae_restrict_mem hK, hmaskall] with c hc hmask
  obtain ⟨w, ⟨z, hz, hRz⟩, hew⟩ := hc
  have hec : e (R z) = c :=
    (congrArg e (show R z = w from hRz)).trans (show e w = c from hew)
  have href : ref c ∈ C.roots := by rw [← hec, hrecover z hz]; exact hz
  have hcoord : e (R (ref c)) = c := by rw [← hec, hrecover z hz]
  have hcoordFull := hcoord
  dsimp only [C, S, R, e] at hcoordFull
  intro H hH hH0 hsupport color
  obtain ⟨B, hB, hsupport⟩ := hsupport
  obtain ⟨k, hk⟩ := exists_nat_gt B
  have hsupport' : ∀ p, p.1 ∉ closedBall 0 ((k : ℝ) + 1) → H p = 0 := by
    intro p hp
    apply hsupport p
    intro hpB
    exact hp ((closedBall_subset_closedBall (by linarith : B ≤ (k : ℝ) + 1)) hpB)
  have ht := D.original_scaled_cell_laplace_tendsto_at hF hcomplete hu ha hinj i
    href s hs hlarge H hH hH0 (by positivity : 0 < (k : ℝ) + 1) hsupport'
    (by simpa only [hcoordFull] using hmask k) color
  simpa only [hcoordFull] using ht

/-- The actual two original iid arrays have the local Poisson Laplace
functional at ONE common full-measure root set. Deterministic endpoint masks
remain inside each test and both full original probability product laws remain
the integration laws. The geometric one-point limits are proved above, so no
scaled-defect or Laplace-convergence callback is an assumption. -/
theorem PopulationLocalPressureCore.original_ae_twoColor_iid_laplace_tendsto
    [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (hnormalization : ∀ n,
      s n ^ finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker =
        ((n + 1 : ℕ) : ℝ)) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let mask := a ⁻¹' C.roots
    ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ (H G : (Fin q → ℝ) × ℝ → ℝ), Measurable H → Measurable G →
        (∀ p, 0 ≤ H p) → (∀ p, 0 ≤ G p) →
        (∃ B : ℝ, 0 < B ∧ ∀ p, p.1 ∉ closedBall 0 B → H p = 0) →
        (∃ B : ℝ, 0 < B ∧ ∀ p, p.1 ∉ closedBall 0 B → G p = 0) →
        let obs := fun n x ↦ (s n • (e (R (a x)) - c), u x)
        let θ := originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
        Tendsto (fun n ↦
          ∫ z : (Fin (n + 1) → M) × (Fin (n + 1) → M),
            Real.exp (-((∑ j : Fin (n + 1), mask.indicator
                (fun x ↦ H (obs n x)) (z.1 j)) +
              (∑ j : Fin (n + 1), mask.indicator
                (fun x ↦ G (obs n x)) (z.2 j))))
            ∂(Measure.pi (fun _ : Fin (n + 1) ↦ η₀)).prod
              (Measure.pi (fun _ : Fin (n + 1) ↦ η₁))) atTop
          (𝓝 (Real.exp (-(θ *
            ((∫ p, 1 - Real.exp (-H p)
                ∂((volume : Measure (Fin q → ℝ)).prod (condDistrib u a η₀ (ref c)))) +
              (∫ p, 1 - Real.exp (-G p)
                ∂((volume : Measure (Fin q → ℝ)).prod (condDistrib u a η₁ (ref c))))))))) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let mask := a ⁻¹' C.roots
  have hmask : MeasurableSet mask := C.roots_compact.measurableSet.preimage ha
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  filter_upwards [D.original_ae_scaled_cell_laplace_tendsto hF hcomplete hu ha hinj i s hs hlarge]
    with c hc
  intro H G hH hG hH0 hG0 hsupportH hsupportG
  let obs := fun n x ↦ (s n • (e (R (a x)) - c), u x)
  let f := fun n x ↦ H (obs n x)
  let g := fun n x ↦ G (obs n x)
  have hobs n : Measurable (obs n) := by
    change Measurable (fun x ↦ (s n • (e (R (a x)) - c), u x))
    exact (((e.continuous.measurable.comp (hR.comp ha)).sub_const c).const_smul (s n)).prodMk
      hu.continuous.measurable
  have hS := hc H hH hH0 hsupportH (0 : Fin 2)
  have hT := hc G hG hG0 hsupportG (1 : Fin 2)
  simp only [hnormalization, populationTwoColorClockKernel, ite_true, one_ne_zero, ite_false] at hS hT
  have hlimit := OTSelector.Probability.tendsto_integral_exp_neg_twoMaskedIidSums
    (X := fun _ ↦ M) (Y := fun _ ↦ M) (fun _ ↦ η₀) (fun _ ↦ η₁)
    (fun n ↦ n + 1) (fun n ↦ n + 1) (fun _ ↦ mask) (fun _ ↦ mask) f g
    (tendsto_add_atTop_nat 1) (tendsto_add_atTop_nat 1)
    (fun _ ↦ hmask) (fun _ ↦ hmask)
    (fun n ↦ hH.comp (hobs n)) (fun n ↦ hG.comp (hobs n))
    (fun n x ↦ hH0 (obs n x)) (fun n x ↦ hG0 (obs n x)) hS hT
  simpa only [mul_add] using hlimit

end ActualCore

end OTSelector.Reconstruction

