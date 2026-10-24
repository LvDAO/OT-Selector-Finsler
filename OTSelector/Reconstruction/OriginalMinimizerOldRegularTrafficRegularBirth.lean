import OTSelector.Reconstruction.OriginalMinimizerRightCommonScaleTraffic
import OTSelector.Reconstruction.OriginalRegularBirthTraffic
import OTSelector.Reconstruction.OriginalRegularBirthMomentumBudget
import OTSelector.Reconstruction.FinslerOriginalAnchorConfinedTrafficAELtwo
import OTSelector.Reconstruction.BirthTrafficSourceWindowVolume
import OTSelector.Probability.RegularBirthConfinedQuadraticPower
import OTSelector.MeasureTheory.Integral.MaskedProductBound

/-! Actual regular scalar-frame moments retain the original same-band kinetic budget. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual scalar canonical momentum has its physical sqrt(s) upper bound. -/
theorem scalar_birthNormalizer_momentum_norm_le {s : ℝ} (hs : 0 < s) (p : ι → ℝ) :
    ‖((positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ)))ᵀ)⁻¹ *ᵥ p‖ ≤
      Real.sqrt s * Real.sqrt (Fintype.card ι : ℝ) * ‖p‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt hs.le,Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [mul_assoc] using scalar_birthNormalizer_momentum_sq_le hs p

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- The unchanged compact regular kernel internally gives the true scalar
momentum times physical occupation bound, without a focal residue. -/
theorem exists_original_regularBirth_momentum_occupation_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo D.lo D.hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ {s : ℝ}, 0 < s →
      ∀ m : PhysicalPairPalmMark (Fin q), ∀ c : ℝ, c-S.level ∈ J →
        ‖((positiveMatrixNormalizer (s • (1 : Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ * ‖originalSeedClockOccupation S w c m‖ ≤
            (C * Real.sqrt s) * ‖originalSeedPairMomentum S w m‖ ^ 2 := by
  obtain ⟨C₀,hC₀⟩ := hJ.exists_bound_of_continuousOn
    ((D.original_kernel_regular hF hw).1.mono hJI)
  let B := max C₀ 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨B * (Real.sqrt (q:ℝ)+1),by positivity,?_⟩
  intro s hs m c hc
  have hv : ‖originalSeedClockOccupation S w c m‖ ≤ B * ‖originalSeedPairMomentum S w m‖ :=
    (norm_originalSeedClockOccupation_le_velocity S w m c).trans
      ((Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right ((hC₀ _ hc).trans (le_max_left _ _)) (norm_nonneg _)))
  have hp := scalar_birthNormalizer_momentum_norm_le hs (originalSeedPairMomentum S w m)
  simp only [Fintype.card_fin] at hp
  calc
    _ ≤ (Real.sqrt s * Real.sqrt (q:ℝ) * ‖originalSeedPairMomentum S w m‖) *
        (B * ‖originalSeedPairMomentum S w m‖) := mul_le_mul hp hv (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      have hz0 : 0 ≤ B * Real.sqrt s * ‖originalSeedPairMomentum S w m‖^2 := by positivity
      nlinarith only [hz0]

/-- A real regular physical clock window has the actual inverse-coarse-scale
weighted Palm rate A C s² times its own original band momentum energy. -/
theorem exists_original_regularBirth_weightedPalm_square_rate
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo D.lo D.hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ {gap diameter : ℝ}, 0 < gap →
      ConditionalClockSupportBounds μ ν gap diameter → ∀ {g : ℝ → ℝ → ℝ}
      (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g),
      ∀ {s A : ℝ}, 0 < s → 0 ≤ A →
      ∀ {B : Set (PhysicalPairPalmMark (Fin q))}, MeasurableSet B →
      ∀ {I : Set ℝ}, MeasurableSet I → volume I ≤ ENNReal.ofReal (A*s) →
        (∀ c ∈ I, c-S.level ∈ J) →
      ∀ (mask : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞),
        (∀ z, mask z ≤ 1) → (∀ m c, m ∉ B ∨ c ∉ I → mask (m,c) = 0) →
      let weighted := ∫⁻ m, ∫⁻ c : ℝ,
        ENNReal.ofReal ‖((positiveMatrixNormalizer (s • (1 : Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m,c))
        ∂volume ∂legalMarkedJointPalm q Q.law
      weighted ≠ (∞:ℝ≥0∞) ∧ Real.sqrt s * weighted.toReal ≤
        A*C*s^2 * (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
          ∂legalMarkedJointPalm q Q.law).toReal := by
  obtain ⟨C,hC,hproduct⟩ := D.exists_original_regularBirth_momentum_occupation_bound hF hw hJ hJI
  refine ⟨C,hC,?_⟩
  intro gap diameter hgap hbounds g Q s A hs hA B hB I hI hlen hclock mask hm hz
  dsimp only
  let energy := ∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
    ∂legalMarkedJointPalm q Q.law
  let weighted := ∫⁻ m, ∫⁻ c : ℝ,
    ENNReal.ofReal ‖((positiveMatrixNormalizer (s • (1 : Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹ *ᵥ
      originalSeedPairMomentum S w m‖ *
      (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m,c))
    ∂volume ∂legalMarkedJointPalm q Q.law
  have he : Measurable (fun m : PhysicalPairPalmMark (Fin q) ↦
      ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)) :=
    ((measurable_originalSeedPairMomentum S hF hw).norm.pow_const 2).ennreal_ofReal
  have hbound : weighted ≤ volume I * ENNReal.ofReal (C*Real.sqrt s) * energy := by
    have h := lintegral_masked_band_product_le (legalMarkedJointPalm q Q.law) volume hB hI
      (fun z : PhysicalPairPalmMark (Fin q) × ℝ ↦
        ENNReal.ofReal ‖((positiveMatrixNormalizer (s • (1 : Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w z.1‖ *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z))
      measurable_const he (ENNReal.ofReal (C*Real.sqrt s)) 0 1
      (e := fun _ ↦ 0) (v := fun m ↦ ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2))
      (by
        intro m _ c hc
        simp only [zero_mul,one_mul,zero_add]
        calc
          _ ≤ ENNReal.ofReal ‖((positiveMatrixNormalizer (s • (1 : Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹ *ᵥ
              originalSeedPairMomentum S w m‖ * ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ :=
            mul_le_mul' le_rfl (mul_le_of_le_one_right (by positivity) (hm (m,c)))
          _ = _ := (ENNReal.ofReal_mul (norm_nonneg _)).symm
          _ ≤ _ := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C*Real.sqrt s)]
            exact ENNReal.ofReal_le_ofReal (hproduct hs m c (hclock c hc)))
      (by intro m c hc; simp only [hz m c hc,mul_zero])
    simpa only [zero_mul,one_mul,zero_add] using h
  have hr : weighted ≤ ENNReal.ofReal ((A*s)*(C*Real.sqrt s)) * energy := by
    calc
      _ ≤ ENNReal.ofReal (A*s) * ENNReal.ofReal (C*Real.sqrt s) * energy :=
        hbound.trans (mul_le_mul' (mul_le_mul' hlen le_rfl) le_rfl)
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A*s)]
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  have hefin : energy ≠ (∞:ℝ≥0∞) := ne_top_of_le_ne_top
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne (setLIntegral_le_lintegral B _)
  have hright := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (A*s)*(C*Real.sqrt s))) hefin
  have hwfin : weighted ≠ (∞:ℝ≥0∞) := ne_top_of_le_ne_top hright hr
  refine ⟨hwfin,?_⟩
  have hre := ENNReal.toReal_mono hright hr
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (A*s)*(C*Real.sqrt s))] at hre
  calc
    _ ≤ Real.sqrt s * (((A*s)*(C*Real.sqrt s))*energy.toReal) :=
      mul_le_mul_of_nonneg_left hre (Real.sqrt_nonneg _)
    _ = A*C*s*energy.toReal*(Real.sqrt s)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hs.le]; ring

/-- An actual compact regular strip provides the full-clock one-edge bound
with the precise sqrt(s) canonical-momentum coefficient, for arbitrary original masks. -/
theorem exists_original_regularBirth_fullClock_canonicalMomentum_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {a b A : ℝ} (hA : 0 ≤ A)
    (ha : a-(S.level:ℝ) ∈ Ioo D.lo D.hi)
    (hb : b-(S.level:ℝ) ∈ Ioo D.lo D.hi) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ c ∈ Icc a b,
      ∀ {l r s R M₀ : ℝ}, l ≤ r → 0 < s → r-l ≤ A*s →
        (∀ v ∈ Icc l r, |v-c| ≤ δ) → 0 ≤ R → 0 ≤ M₀ →
      ∀ η : (Fin q → ℝ) → ℝ, (∀ x,0 ≤ η x) → (∀ x,η x ≤ M₀) →
        (∀ x,R < ‖x‖ → η x = 0) →
      ∀ mask : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞,
        (∀ z,mask z ≤ 1) → (∀ m v,v ∉ Icc l r → mask (m,v) = 0) →
        (∀ m v,mask (m,v) ≠ 0 → m.1.1-(S.level:ℝ) ∈ Ioo D.lo D.hi) →
      ∀ x : Fin q → ℝ, ∀ m : PhysicalPairPalmMark (Fin q),
        (∫⁻ v : ℝ, ENNReal.ofReal (η (x+originalSeedPathOffset S w v m)) *
          (ENNReal.ofReal ‖originalSeedClockOccupation S w v m‖ * mask (m,v))) ≤
        ENNReal.ofReal ((4*M₀*(R+1)*C)*Real.sqrt s) *
          ENNReal.ofReal ‖((positiveMatrixNormalizer (s • (1:Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := D.exists_original_regular_birth_maskedTraffic hF hw hA ha hb
  refine ⟨C,δ,hC,hδ,?_⟩
  intro c hc l r s R M₀ hlr hs hlen hwin hR hM η hη0 hηM hηR mask hm hz hsource x m
  by_cases hmI : m.1.1-(S.level:ℝ) ∈ Ioo D.lo D.hi
  · have hloc := hbound c hc hlr hs hlen hwin hR hM x m hmI η hη0 hηM hηR
      (fun v ↦ mask (m,v)) (fun v _ ↦ hm (m,v))
    have heq := setLIntegral_eq_of_ae_zero_outside (μ := (volume:Measure ℝ)) measurableSet_Icc
      (u := fun v : ℝ ↦ ENNReal.ofReal (η (x+originalSeedPathOffset S w v m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w v m‖ * mask (m,v)))
      (ae_of_all _ (fun v hv ↦ by rw [hz m v hv,mul_zero,mul_zero]))
    rw [← heq]
    have hloc' : (∫⁻ v in Icc l r, ENNReal.ofReal (η (x+originalSeedPathOffset S w v m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w v m‖ * mask (m,v))) ≤
      ENNReal.ofReal ((4*M₀*(R+1))*min 1 ((C*Real.sqrt s)*
        ‖((positiveMatrixNormalizer (s • (1:Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖)) := by
      simpa only [originalSeedCompletePath_eq_anchor_add_offset,mul_assoc] using hloc
    apply hloc'.trans
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4*M₀*(R+1)*C)*Real.sqrt s)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (4*M₀*(R+1))*((C*Real.sqrt s)*
          ‖((positiveMatrixNormalizer (s • (1:Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by ring
  · have hzero : ∀ v,mask (m,v) = 0 := by
      intro v
      by_contra hn
      exact hmI (hsource m v hn)
    simp only [hzero,mul_zero,lintegral_zero]
    exact zero_le

/-- Actual regular confined traffic has its same-band K s² momentum bound.
Original geometry supplies the one-edge gain and the original kinetic law supplies
all moment finiteness. The marked anchor may be the source or target displacement. -/
theorem exists_original_regularBirth_confined_smallSecondMoment
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {a b A : ℝ} (hA : 0 ≤ A)
    (ha : a-(S.level:ℝ) ∈ Ioo D.lo D.hi)
    (hb : b-(S.level:ℝ) ∈ Ioo D.lo D.hi) (Rwindow : ℝ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ c ∈ Icc a b,
      ∀ {gap diameter : ℝ}, 0 < gap → ConditionalClockSupportBounds μ ν gap diameter →
      ∀ {g : ℝ → ℝ → ℝ}
        (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g),
      ∀ {l r s R M₀ K : ℝ}, l ≤ r → 0 < s → r-l ≤ A*s →
        (∀ v ∈ Icc l r, |v-c| ≤ δ) → 0 ≤ R → 0 ≤ M₀ → 0 ≤ K →
      ∀ {η : (Fin q → ℝ) → ℝ}, Measurable η → (∀ x,0 ≤ η x) → (∀ x,η x ≤ M₀) →
        (∀ x,R < ‖x‖ → η x = 0) →
      ∀ mask : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞,
        Measurable mask → (∀ z,mask z ≤ 1) → (∀ m v,v ∉ Icc l r → mask (m,v) = 0) →
        (∀ m v,mask (m,v) ≠ 0 → m.1.1-(S.level:ℝ) ∈ Ioo D.lo D.hi) →
      ∀ anchor : PhysicalPairPalmMark (Fin q) → Fin q → ℝ, Measurable anchor →
      ∀ {Bad : Set (LegalMarkedOptimalInputScene q)}, MeasurableSet Bad →
      ∀ {B : Set (PhysicalPairPalmMark (Fin q))}, MeasurableSet B →
      ∀ V : LegalMarkedOptimalInputScene q → Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)),
        (∀ scene,MeasurableSet (V scene)) →
      let d := fun z : PhysicalPairPalmMark (Fin q) × ℝ ↦ originalSeedPathOffset S w z.2 z.1
      let f := fun z : PhysicalPairPalmMark (Fin q) × ℝ ↦
        ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
      (∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)), scene ∉ Bad →
        (∀ p ∈ V scene,p.1+anchor p.2 ∈ birthTrafficSpatialWindow (0:Matrix (Fin q) (Fin q) ℝ)
          1 s Rwindow ∧ p.2 ∈ B) ∧
        physicalScenePairKernel scene.1 (V scene) ≤ ENNReal.ofReal K ∧
        (∀ᵐ p ∂physicalScenePairKernel scene.1,p ∉ V scene →
          (∫⁻ v : ℝ,ENNReal.ofReal (η (p.1+d (p.2,v)))*f (p.2,v)) = 0)) →
      MemLp (Badᶜ.indicator (fun scene ↦
        (legalMarkedCompletePathTraffic q d (fun x ↦ ENNReal.ofReal (η x)) f scene).toReal))
        2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ scene,(Badᶜ.indicator (fun z ↦
        (legalMarkedCompletePathTraffic q d (fun x ↦ ENNReal.ofReal (η x)) f z).toReal) scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      K*(4*M₀*(R+1))^2*C*s^2*
        (∫⁻ m in B,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
          ∂legalMarkedJointPalm q Q.law).toReal := by
  obtain ⟨C₀,δ,hC₀,hδ,hsingle⟩ :=
    D.exists_original_regularBirth_fullClock_canonicalMomentum_bound hF hw hA ha hb
  obtain ⟨Cv,hCv,hvol⟩ := exists_birthTrafficSpatialWindow_volume_bound
    (Matrix.PosSemidef.zero (n := Fin q)) (by simpa only [Fintype.card_fin] using hq) Rwindow
  refine ⟨C₀^2*Cv*(q:ℝ),δ,by positivity,hδ,?_⟩
  intro c hc gap diameter hgap hbounds g Q l r s R M₀ K hlr hs hlen hwin hR hM hK
    η hη hη0 hηM hηR mask hmask hm hz hsource anchor hanchor Bad hBad B hB V hV
  dsimp only
  intro hdata
  have hLp := D.goodEvent_original_anchorConfined_traffic_memLp_two_ae hF hw hgap hbounds Q
    anchor hanchor ((positiveMatrixNormalizer (s • (1:Matrix (Fin q) (Fin q) ℝ)))ᵀ)⁻¹
    hη.ennreal_ofReal mask hmask hBad
    (isCompact_birthTrafficSpatialWindow (0:Matrix (Fin q) (Fin q) ℝ) 1 s Rwindow).measurableSet
    (isCompact_birthTrafficSpatialWindow (0:Matrix (Fin q) (Fin q) ℝ) 1 s Rwindow).measure_ne_top
    hB V hV hK (show 0 ≤ (4*M₀*(R+1)*C₀)*Real.sqrt s by positivity) (by
      filter_upwards [hdata] with scene hscene
      intro hn
      obtain ⟨hanchor,hcount,hzero⟩ := hscene hn
      refine ⟨hanchor,hcount,hzero,Filter.Eventually.of_forall (fun p ↦ ?_)⟩
      exact hsingle c hc hlr hs hlen hwin hR hM η hη0 hηM hηR mask hm hz hsource p.1 p.2)
  have hvol' : (volume (birthTrafficSpatialWindow (0:Matrix (Fin q) (Fin q) ℝ) 1 s Rwindow)).toReal ≤ Cv := by
    have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvol zero_lt_one le_rfl hs)
    simpa only [one_pow,inv_one,mul_one,ENNReal.toReal_ofReal hCv.le] using hv
  have hmoment := D.original_regular_birthNormalizer_quadraticMoment_toReal_le hF hw hgap hbounds Q hs B
  have hpower := regularBirth_confined_quadratic_power_bound («q» := q) (C := 4*M₀*(R+1)*C₀)
    hs hCv.le hK ENNReal.toReal_nonneg hvol' hmoment
  refine ⟨hLp.1,hLp.2.trans (hpower.trans_eq ?_)⟩
  congr 1
  ring

/-- Scalar regular source phase cells have uniformly bounded original-input
intensity. The exact Haar normalization and original probability mass suffice;
no density estimate or law for selected contributors is assumed. -/
theorem exists_original_regularBirth_sourcePhaseCell_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q) (Rcell : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {s Ddet : ℝ}, 0 < s → 0 ≤ Ddet →
      ∀ {cut : ℝ}, cut ∈ Ioo D.lo D.hi →
      ∀ {Band : Set ℝ}, MeasurableSet Band →
      let T := positiveMatrixNormalizer (s • (1:Matrix (Fin q) (Fin q) ℝ))
      let δ := (Real.sqrt s)⁻¹
      ∀ z₀ p₀, ((volume : Measure (Fin q → ℝ)).prod μ)
        (D.commonScaleOriginalSourcePhaseCell T cut δ
          (D.originalBirthSourceDetCarrier T cut Band Ddet) z₀ p₀ Rcell) ≤
            ENNReal.ofReal (C*Ddet) := by
  obtain ⟨C,hC,hcell⟩ := D.exists_commonScaleOriginalSourcePhaseCell_birth_intensity
    hF hw (Matrix.PosSemidef.zero (n := Fin q)) hq Rcell
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  refine ⟨C,hC,?_⟩
  intro s Ddet hs hD cut hcut Band hBand
  dsimp only
  have hmass : μ Band ≤ ENNReal.ofReal (s⁻¹*(1:ℝ)^((0:Matrix (Fin q) (Fin q) ℝ).rank)*s) := by
    simpa only [one_pow,mul_one,inv_mul_cancel₀ hs.ne',ENNReal.ofReal_one] using
      (prob_le_one (μ := μ) (s := Band))
  have hb := hcell zero_lt_one le_rfl hs hD (inv_nonneg.mpr hs.le) hcut hBand hmass
  intro z₀ p₀
  have heq : C*Ddet*s⁻¹*(s/(1:ℝ)) = C*Ddet := by field_simp
  simpa only [birthResidueScale,smul_zero,add_zero,birthTrafficCoarseScale,
    Real.one_rpow,mul_one,heq] using hb z₀ p₀

/-- The target version keeps the original target law and its target phase
cell, so its marked physical confinement uses the actual target anchor. -/
theorem exists_original_regularBirth_targetPhaseCell_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q) (Rcell : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {s Ddet : ℝ}, 0 < s → 0 ≤ Ddet →
      ∀ {cut : ℝ}, cut ∈ Ioo D.lo D.hi →
      ∀ {Band : Set ℝ}, MeasurableSet Band →
      let T := positiveMatrixNormalizer (s • (1:Matrix (Fin q) (Fin q) ℝ))
      let δ := (Real.sqrt s)⁻¹
      ∀ z₀ p₀, ((volume : Measure (Fin q → ℝ)).prod ν)
        (D.commonScaleOriginalTargetPhaseCell T cut δ
          (D.originalBirthTargetDetCarrier T cut Band Ddet) z₀ p₀ Rcell) ≤
            ENNReal.ofReal (C*Ddet) := by
  obtain ⟨C,hC,hcell⟩ := D.exists_commonScaleOriginalTargetPhaseCell_birth_intensity
    hF hw (Matrix.PosSemidef.zero (n := Fin q)) hq Rcell
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  refine ⟨C,hC,?_⟩
  intro s Ddet hs hD cut hcut Band hBand
  dsimp only
  have hmass : ν Band ≤ ENNReal.ofReal (s⁻¹*(1:ℝ)^((0:Matrix (Fin q) (Fin q) ℝ).rank)*s) := by
    simpa only [one_pow,mul_one,inv_mul_cancel₀ hs.ne',ENNReal.ofReal_one] using
      (prob_le_one (μ := ν) (s := Band))
  have hb := hcell zero_lt_one le_rfl hs hD (inv_nonneg.mpr hs.le) hcut hBand hmass
  intro z₀ p₀
  have heq : C*Ddet*s⁻¹*(s/(1:ℝ)) = C*Ddet := by field_simp
  simpa only [birthResidueScale,smul_zero,add_zero,birthTrafficCoarseScale,
    Real.one_rpow,mul_one,heq] using hb z₀ p₀

/-- The original compact regular kernel controls its actual compliance curve
uniformly in every scalar birth frame, including the physical Lipschitz constant. -/
theorem exists_original_regularBirth_complianceCurve_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo D.lo D.hi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {s cut ell : ℝ}, 0 < s →
      uIcc (cut-S.level) (cut-S.level+ell) ⊆ J →
      let T := positiveMatrixNormalizer (s • (1:Matrix (Fin q) (Fin q) ℝ))
      originalNormalizedClockMobility S w T cut ell 0 = 0 ∧
      (∀ r ∈ Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T cut ell r‖ ≤ B*|ell|/s) ∧
      ∀ r ∈ Icc (0:ℝ) 1,∀ v ∈ Icc (0:ℝ) 1,
        ‖originalNormalizedClockMobility S w T cut ell r -
          originalNormalizedClockMobility S w T cut ell v‖ ≤ (B*|ell|/s)*|r-v| := by
  obtain ⟨κ,C,hκ,hC,hscalar⟩ := D.exists_original_kernel_compact_twoSided_bounds hF hw hJ hJI
  obtain ⟨B,hB,hbound⟩ := exists_norm_bound_birth_normalized_mobility (ι := Fin q) C
  refine ⟨B,hB,?_⟩
  intro s cut ell hs hwindow
  dsimp only
  apply D.originalNormalizedClockMobility_bounds hF hw _ hs hB (hwindow.trans hJI)
  intro v hv
  have hu : (C • ((1:ℝ)^2)⁻¹ • (0:Matrix (Fin q) (Fin q) ℝ) + C • 1 -
      originalSeedKernel S w v).PosSemidef := by
    simpa only [smul_zero,zero_add] using (hscalar v (hwindow hv)).2
  have hu' : (C • (((1:ℝ)^2)⁻¹ • (0:Matrix (Fin q) (Fin q) ℝ) + 1) -
      originalSeedKernel S w v).PosSemidef := by
    simpa only [smul_zero,zero_add] using hu
  have h := hbound (Matrix.PosSemidef.zero (n := Fin q))
    ((D.original_kernel_regular hF hw).2 v (hJI (hwindow hv))).posSemidef
    zero_lt_one hs (by norm_num : (1:ℝ) ∈ Icc (1/2) (4*1)) hC.le hu'
  simpa only [birthResidueScale,smul_zero,add_zero] using h

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
