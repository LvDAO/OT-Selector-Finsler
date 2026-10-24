import OTSelector.Reconstruction.OriginalIIDActualLocalLaplace
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicLabelGeometry
import OTSelector.MeasureTheory.ScaledDensityMask

/-!
# Original iid local Laplace limits on the full fixed seed

The compact core is used only to identify the limiting density and clock laws.
Original population mass outside that core vanishes at almost every retained
coordinate root, so the same limit holds on the unchanged full seed mask.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Metric Module Manifold OTSelector.Geometry
open scoped Topology ENNReal NNReal ContDiff BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- A bounded observable supported in one small coordinate ball differs between
a full source piece and its exact retained coordinate core only by the original
pushed-forward mass of the missing coordinate region. -/
theorem original_integral_full_mask_sub_core_le_missing_mass
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [MetricSpace V] [BorelSpace V]
    (η : Measure Ω) [IsFiniteMeasure η] {A B : Set Ω} {K : Set V}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hK : MeasurableSet K)
    {φ : Ω → V} (hφ : Measurable φ) (hexact : A = B ∩ φ ⁻¹' K)
    (c : V) (R : ℝ) {g : Ω → ℝ} (hg : Measurable g)
    (hbound : ∀ x, ‖g x‖ ≤ 1) (hsupport : ∀ x, φ x ∉ closedBall c R → g x = 0) :
    |(∫ x in B, g x ∂η) - ∫ x in A, g x ∂η| ≤
      (η.map φ).real (closedBall c R \ K) := by
  have hsub : A ⊆ B := hexact ▸ inter_subset_left
  have hgi : Integrable g η := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall hbound)
  let T := (B \ A) ∩ φ ⁻¹' closedBall c R
  have hT : MeasurableSet T := (hB.diff hA).inter (isClosed_closedBall.measurableSet.preimage hφ)
  have hlocal : (∫ x in B \ A, g x ∂η) = ∫ x in T, g x ∂η := by
    apply original_setIntegral_localize η (hB.diff hA) inter_subset_left
    intro x hx
    apply hsupport x
    intro hxball
    exact hx.2 ⟨hx.1, hxball⟩
  have hTsub : T ⊆ φ ⁻¹' (closedBall c R \ K) := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    intro hxK
    exact hx.1.2 (hexact ▸ ⟨hx.1.1, hxK⟩)
  rw [← setIntegral_sdiff hA hgi.integrableOn hsub, hlocal, ← Real.norm_eq_abs]
  calc
    _ ≤ 1 * η.real T := norm_setIntegral_le_of_norm_le_const (measure_lt_top η T)
      (fun x _ ↦ hbound x)
    _ ≤ (η.map φ).real (closedBall c R \ K) := by
      rw [one_mul, measureReal_def, measureReal_def, Measure.map_apply hφ
        (isClosed_closedBall.measurableSet.diff hK)]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hTsub)

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

omit [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure] in
/-- On its fixed original seed piece, belonging to the retained core is exactly
belonging to the retained coordinate image. -/
theorem PopulationLocalPressureCore.original_core_mask_eq_full_seed_inter_coordinate
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
    a ⁻¹' C.roots =
      physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex ∩
        (fun x ↦ e (R (a x))) ⁻¹' (e '' (R '' C.roots)) := by
  dsimp only
  let C := D.haar.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
  ext x
  constructor
  · intro hx
    exact ⟨C.roots_subset_piece hx, ⟨R (a x), ⟨a x, hx, rfl⟩, rfl⟩⟩
  · rintro ⟨hx, w, ⟨z, hz, hRz⟩, hew⟩
    have hRax : R z = R (a x) := e.injective ((congrArg e hRz).trans hew)
    have hzx : z = a x := fixed_seed_rootLabel_injOn hF hcomplete hu ha hinj C.seedIndex
      (C.roots_subset_piece hz) hx hRax
    change a x ∈ C.roots
    rw [← hzx]
    exact hz

/-- At almost every retained coordinate root, the SAME fixed whole-seed source
has the local original-intensity Laplace defect limit. Arbitrary original mass
outside the retained core is removed by differentiation of its finite coordinate
pushforward, without a density bound outside the core. -/
theorem PopulationLocalPressureCore.original_ae_full_seed_scaled_laplace_tendsto
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
    let full := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
    ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ (H : (Fin q → ℝ) × ℝ → ℝ), Measurable H → (∀ p, 0 ≤ H p) →
        (∃ B : ℝ, 0 < B ∧ ∀ p, p.1 ∉ closedBall 0 B → H p = 0) →
      ∀ color : Fin 2,
        let η := if color = 0 then η₀ else η₁
        let α := populationTwoColorClockKernel u a η₀ η₁ color (ref c)
        Tendsto (fun n ↦ s n ^ q *
          ∫ x in full,
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
  let φ := fun x ↦ e (R (a x))
  let full := physicalSceneOriginalSeedSource
    (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  have hC : MeasurableSet C.roots := C.roots_compact.measurableSet
  have hA : MeasurableSet (R '' C.roots) :=
    D.haar.measurable_cell_label_image hcomplete i hC Subset.rfl
  have hK : MeasurableSet K := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hA
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hφ : Measurable φ := e.continuous.measurable.comp (hR.comp ha)
  have hfull : MeasurableSet full := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj C.seedIndex
  have hexact : a ⁻¹' C.roots = full ∩ φ ⁻¹' K :=
    D.original_core_mask_eq_full_seed_inter_coordinate hF hcomplete hu ha hinj i
  let η : Fin 2 → Measure M := fun color ↦ if color = 0 then η₀ else η₁
  have hη (color : Fin 2) : IsFiniteMeasure (η color) := by
    dsimp only [η]
    split_ifs <;> infer_instance
  let τ := fun color ↦ (η color).map φ
  have hτ (color : Fin 2) : IsFiniteMeasure (τ color) := inferInstance
  have hmissing : ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ k : ℕ, ∀ color : Fin 2,
        Tendsto (fun n ↦ s n ^ q *
          ((τ color) (closedBall c (((k : ℝ) + 1) / s n) \ K)).toReal) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro color
    exact OTSelector.Probability.ae_tendsto_scaled_missing_mass
      (τ color) hK s hs hlarge (by positivity)
  filter_upwards [D.original_ae_scaled_cell_laplace_tendsto hF hcomplete hu ha hinj i
    s hs hlarge, hmissing] with c hcore hmissing
  intro H hH hH0 hsupport color
  obtain ⟨B, hB, hsupport⟩ := hsupport
  obtain ⟨k, hk⟩ := exists_nat_gt B
  have hsupport' : ∀ p, p.1 ∉ closedBall 0 ((k : ℝ) + 1) → H p = 0 := by
    intro p hp
    apply hsupport p
    intro hpB
    exact hp ((closedBall_subset_closedBall (by linarith : B ≤ (k : ℝ) + 1)) hpB)
  let g := fun n x ↦ 1 - Real.exp (-H (s n • (φ x - c), u x))
  have hgm n : Measurable (g n) := by
    apply measurable_const.sub
    apply Measurable.exp
    apply Measurable.neg
    exact hH.comp (((hφ.sub_const c).const_smul (s n)).prodMk hu.continuous.measurable)
  have hgb n x : ‖g n x‖ ≤ 1 := by
    have he : Real.exp (-H (s n • (φ x - c), u x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hH0 _))
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [g]; linarith)]
    dsimp only [g]
    linarith [Real.exp_pos (-H (s n • (φ x - c), u x))]
  have hgz n x (hx : φ x ∉ closedBall c (((k : ℝ) + 1) / s n)) : g n x = 0 := by
    have hout : s n • (φ x - c) ∉ closedBall 0 ((k : ℝ) + 1) := by
      intro hscaled
      apply hx
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (hs n)] at hscaled
      rw [mem_closedBall, dist_eq_norm]
      exact (le_div_iff₀ (hs n)).mpr (by nlinarith)
    simp only [g, hsupport' (s n • (φ x - c), u x) hout, neg_zero, Real.exp_zero, sub_self]
  have herr : Tendsto (fun n ↦ s n ^ q *
      ((∫ x in full, g n x ∂η color) - ∫ x in a ⁻¹' C.roots, g n x ∂η color))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n ↦ s n ^ q *
      ((τ color) (closedBall c (((k : ℝ) + 1) / s n) \ K)).toReal)
    · intro n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (hs n).le q)]
      exact mul_le_mul_of_nonneg_left
        (original_integral_full_mask_sub_core_le_missing_mass (η color)
          (hC.preimage ha) hfull hK hφ hexact c (((k : ℝ) + 1) / s n)
          (hgm n) (hgb n) (hgz n)) (pow_nonneg (hs n).le q)
    · exact hmissing k color
  have hlocal := hcore H hH hH0 ⟨B, hB, hsupport⟩ color
  have hsum := herr.add hlocal
  simp only [zero_add] at hsum
  apply hsum.congr'
  apply Eventually.of_forall
  intro n
  dsimp only [g, φ, η]
  ring

/-- The actual iid arrays on the fixed WHOLE original seed piece have the same
joint local Laplace functional at one universal full-measure retained root set.
The original probability laws stay unchanged and no outside-core density or
Laplace convergence callback is assumed. -/
theorem PopulationLocalPressureCore.original_ae_twoColor_full_seed_iid_laplace_tendsto
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
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
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
  let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) C.seedIndex
  have hmask : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource
    hF hcomplete hu ha hinj C.seedIndex
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  filter_upwards [D.original_ae_full_seed_scaled_laplace_tendsto hF hcomplete hu ha hinj i s hs hlarge]
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
