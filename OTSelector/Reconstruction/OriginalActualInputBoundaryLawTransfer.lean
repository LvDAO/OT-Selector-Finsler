import OTSelector.Reconstruction.OriginalInputBoundaryWeightVariance
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowLaw
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# The actual stationary matching retains its full original boundary-input law

The spatial cutoff is independent of clock and color. Hence the original compact
Laplace data identify a complete spatial-window restriction with all original
marks retained. Signed class readouts are then transferred on the same scene law.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

local instance actualInputBoundaryLawTransferInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance actualInputBoundaryLawTransferPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- A spatial cutoff retains the entire clock axis and both original colors.
The containing original Poisson cube can be required to exceed any fixed radius. -/
theorem LegalWeightedStationaryPoissonMatching.map_fullSpatialInputRestriction_eq_originalPoisson
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (Rmin : ℝ) :
    ∃ S > 0, Rmin ≤ S ∧
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)).restrict
          ((K ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set (Fin 2)))) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ (legalInputTwoBlockMeasure q b).restrict
          ((K ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set (Fin 2)))) := by
  obtain ⟨η, hηK, hη⟩ := LocalFiniteMeasure.exists_compact_cutoff hK
  obtain ⟨S0, hS0, hbound⟩ := η.hasCompactSupport.isBounded.exists_pos_norm_lt
  let S := max S0 Rmin + 1
  have hS : 0 < S := by dsimp only [S]; linarith [le_max_left S0 Rmin]
  have hRS : Rmin ≤ S := by dsimp only [S]; linarith [le_max_right S0 Rmin]
  let U : Set (LegalColoredInputPoint q) := (K ×ˢ univ) ×ˢ univ
  have hU : MeasurableSet U := (hK.measurableSet.prod MeasurableSet.univ).prod
    MeasurableSet.univ
  let χ : C(LegalColoredInputPoint q, ℝ) := η.toContinuousMap.comp
    ⟨fun p ↦ p.1.1, continuous_fst.comp continuous_fst⟩
  have hχ (p : LegalColoredInputPoint q) : 0 ≤ χ p := (hη p.1.1).1
  have hχU : EqOn χ 1 U := fun p hp ↦ hηK hp.1.1
  have hχzero (x : LegalMarkedPhysicalPoint q) (c : Fin 2)
      (hx : x.1 ∉ haarRootCube (Fin q) S) : χ (x, c) = 0 := by
    change η x.1 = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hsupp
    apply hx
    apply (mem_haarRootCube_iff_norm_le hS.le x.1).mpr
    exact (hbound _ hsupp).le.trans (by dsimp only [S]; linarith [le_max_left S0 Rmin])
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have : IsProbabilityMeasure
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) :=
    isProbabilityMeasure_legalInputPoissonWindowLaw q hS.le measurableSet_Icc
      (Subset.refl _) hvol α β
  let P := (M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd
  let P' := (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
    (legalInputTwoBlockLocal q)
  have : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have : IsProbabilityMeasure P' :=
    Measure.isProbabilityMeasure_map (measurable_legalInputTwoBlockLocal q).aemeasurable
  have hLap : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 χ,
          fun x ↦ mul_nonneg (F.2 x) (hχ x)⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 χ,
          fun x ↦ mul_nonneg (F.2 x) (hχ x)⟩ μ ∂P' := by
    intro F
    let T := LocalFiniteMeasure.weightedContinuousTest F.1 χ
    have hT (x) : 0 ≤ T x := mul_nonneg (F.2 x) (hχ x)
    have hzero (x : LegalMarkedPhysicalPoint q) (c : Fin 2)
        (hx : x.1 ∉ haarRootCube (Fin q) S) : T (x, c) = 0 := by
      change F.1 (x, c) * χ (x, c) = 0
      rw [hχzero x c hx, mul_zero]
    change (∫ μ, legalInputMeasureLaplace ⟨T, hT⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace ⟨T, hT⟩ μ ∂P'
    dsimp only [P, P']
    rw [integral_map measurable_snd.aemeasurable
      (legalInputMeasureLaplace ⟨T, hT⟩).continuous.aestronglyMeasurable,
      integral_map (measurable_legalInputTwoBlockLocal q).aemeasurable
        (legalInputMeasureLaplace ⟨T, hT⟩).continuous.aestronglyMeasurable]
    change (∫ s, legalMarkedInputSceneLaplace q T hT s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) = _
    rw [M.input_laplace S hS T hT hzero]
    apply integral_congr_ae
    exact .of_forall fun b ↦ by
      change Real.exp (-(legalInputBlockTest (fun x ↦ T (x, 0)) b.1 +
        legalInputBlockTest (fun x ↦ T (x, 1)) b.2)) =
          Real.exp (-(∫ x, T x ∂legalInputTwoBlockMeasure q b))
      rw [integral_legalInputTwoBlockMeasure]
  have hlaw := map_legalInput_restrict_eq_of_cutoff_laplace P P' χ hχ hU hχU hLap
  have hr : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simpa only [Measure.restrict_apply hV, Function.comp_def] using
      (Measure.measurable_coe (hV.inter hU)).comp measurable_localFiniteMeasure_coe
  refine ⟨S, hS, hRS, ?_⟩
  simpa only [P, P', Measure.map_map hr measurable_snd,
    Measure.map_map hr (measurable_legalInputTwoBlockLocal q), Function.comp_def,
    legalInputTwoBlockLocal] using hlaw

private theorem measurable_signedIntegral_of_measurable {X : Type*} [MeasurableSpace X]
    {f : X → ℝ} (hf : Measurable f) :
    Measurable (fun μ : Measure X ↦ ∫ x, f x ∂μ) := by
  let κ : Kernel (Measure X) X := ⟨id, measurable_id⟩
  exact (hf.stronglyMeasurable.integral_kernel (κ := κ)).measurable

private theorem originalInputColor_signedIntegral_eq_colored {q : ℕ}
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2)
    {f : LegalMarkedPhysicalPoint q → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂legalInputColorMeasure q μ c) =
      ∫ x, {p : LegalColoredInputPoint q | p.2 = c}.indicator (fun p ↦ f p.1) x
        ∂(μ : Measure (LegalColoredInputPoint q)) := by
  rw [legalInputColorMeasure, integral_map measurable_fst.aemeasurable
    hf.aestronglyMeasurable]
  exact (integral_indicator (s := {p : LegalColoredInputPoint q | p.2 = c})
    (μ := (μ : Measure (LegalColoredInputPoint q)))
    (measurable_snd (measurableSet_singleton c))).symm

private theorem originalInputTwoBlock_color_signedIntegral {q : ℕ} (c : Fin 2)
    (f : LegalMarkedPhysicalPoint q → ℝ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    (∫ x, {p : LegalColoredInputPoint q | p.2 = c}.indicator (fun p ↦ f p.1) x
      ∂legalInputTwoBlockMeasure q b) =
      legalInputBlockTest f (if c = 0 then b.1 else b.2) := by
  rw [integral_legalInputTwoBlockMeasure]
  fin_cases c <;> simp [legalInputBlockTest]

/-- Every measurable signed original-input readout supported in a fixed compact
spatial window has its entire original finite Poisson-array law on the same `M`.
The test may use arbitrary unbounded clock classes. -/
theorem LegalWeightedStationaryPoissonMatching.map_fullInput_signedIntegral_eq_originalPoisson
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    {f : LegalMarkedPhysicalPoint q → ℝ} (hf : Measurable f)
    (hsupport : ∀ p, p.1 ∉ K → f p = 0) (c : Fin 2) (Rmin : ℝ) :
    ∃ S > 0, Rmin ≤ S ∧
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ ∫ p, f p ∂legalInputColorMeasure q s.2 c) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ legalInputBlockTest f (if c = 0 then b.1 else b.2)) := by
  obtain ⟨S, hS, hRS, hlaw⟩ := M.map_fullSpatialInputRestriction_eq_originalPoisson hK Rmin
  let U : Set (LegalColoredInputPoint q) := (K ×ˢ univ) ×ˢ univ
  have hU : MeasurableSet U := (hK.measurableSet.prod MeasurableSet.univ).prod
    MeasurableSet.univ
  let F := {p : LegalColoredInputPoint q | p.2 = c}.indicator (fun p ↦ f p.1)
  have hF : Measurable F := (hf.comp measurable_fst).indicator
    (measurable_snd (measurableSet_singleton c))
  let read : Measure (LegalColoredInputPoint q) → ℝ := fun μ ↦ ∫ p, F p ∂μ
  have hr : Measurable read := measurable_signedIntegral_of_measurable hF
  have hrestrict : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simpa only [Measure.restrict_apply hV, Function.comp_def] using
      (Measure.measurable_coe (hV.inter hU)).comp measurable_localFiniteMeasure_coe
  have hleft : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)).restrict U) := hrestrict.comp measurable_snd
  have hright : Measurable (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) :=
    hrestrict.comp (measurable_legalInputTwoBlockLocal q)
  have hzero (x : LegalColoredInputPoint q) (hx : x ∉ U) : F x = 0 := by
    have hnot : x.1.1 ∉ K := fun h ↦ hx ⟨⟨h, mem_univ _⟩, mem_univ _⟩
    by_cases hc : x.2 = c <;> simp [F, hc, hsupport x.1 hnot]
  have hread (μ : Measure (LegalColoredInputPoint q)) : read (μ.restrict U) = ∫ p, F p ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have he := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦ P.map read) hlaw
  rw [Measure.map_map hr hleft, Measure.map_map hr hright] at he
  refine ⟨S, hS, hRS, ?_⟩
  simpa only [Function.comp_def, hread, F,
    originalInputColor_signedIntegral_eq_colored _ c hf,
    originalInputTwoBlock_color_signedIntegral] using he

/-- A full original boundary readout is a genuine measurable random variable
on the actual stationary matching scene. -/
theorem measurable_originalActualInputBoundaryReadout
    {q : ℕ} {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) (R : ℝ)
    {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      ∫ p, originalInputClassBoundaryWeight η R C p ∂legalInputColorMeasure q s.2 c) := by
  have hf := (measurable_originalInputClassBoundaryWeight hη R hC).stronglyMeasurable
  have h := hf.integral_kernel (κ := legalMarkedInputColorKernel q c)
  simpa only [legalMarkedInputColorKernel_apply] using h.measurable

private theorem integral_marked_restrict_spatial_eq_full {q : ℕ}
    (γ : Measure ℝ) [IsProbabilityMeasure γ] {W : Set (Fin q → ℝ)}
    {f : LegalMarkedPhysicalPoint q → ℝ} (hzero : ∀ p, p.1 ∉ W → f p = 0) :
    (∫ p, f p ∂((volume : Measure (Fin q → ℝ)).restrict W).prod γ) =
      ∫ p, f p ∂(volume : Measure (Fin q → ℝ)).prod γ := by
  have heq : ((volume : Measure (Fin q → ℝ)).restrict W).prod γ =
      ((volume : Measure (Fin q → ℝ)).prod γ).restrict (W ×ˢ univ) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure (Fin q → ℝ))) (ν := γ) W univ)
  rw [heq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  exact hzero p (fun hx ↦ hp ⟨hx, mem_univ _⟩)

private theorem originalActualBoundary_blockLaw_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    IsProbabilityMeasure (blockDataLaw ν (fun n ↦ poissonMeasure r {n})) := by
  rw [blockDataLaw_eq_map_cloud]
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_sigma_mk n).comp
    (measurable_pi_lambda _ (fun j : Fin n ↦ measurable_pi_apply (j : ℕ)))

/-- The same actual stationary minimizer has a true full-input second moment,
zero signed boundary mean, and the exact class-factor surface-order variance.
All clock marks and both original colors remain in its original joint law. -/
theorem LegalWeightedStationaryPoissonMatching.original_fullInput_boundaryWeight_variance
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {η : (Fin q → ℝ) → ℝ} (hηm : Measurable η) (hη : Integrable η)
    (hηnonneg : ∀ x, 0 ≤ η x) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    let γ := if c = 0 then α else β
    let I := fun s : LegalMarkedOptimalInputScene q ↦
      ∫ p, originalInputClassBoundaryWeight η R C p ∂legalInputColorMeasure q s.2 c
    MemLp I 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, I s ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) = 0 ∧
      variance I (M.law : Measure (LegalMarkedOptimalInputScene q)) =
        γ.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 ∧
      variance I (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        γ.real C * ((4 * (q : ℝ) * 4 ^ (q - 1)) * R ^ (q - 1)) := by
  let γ := if c = 0 then α else β
  have : IsProbabilityMeasure γ := by
    by_cases hc : c = 0 <;> simp only [γ, hc, ↓reduceIte] <;> infer_instance
  let f := originalInputClassBoundaryWeight η R C
  let I := fun s : LegalMarkedOptimalInputScene q ↦
    ∫ p, f p ∂legalInputColorMeasure q s.2 c
  have hf : Measurable f := measurable_originalInputClassBoundaryWeight hηm R hC
  have hb : ∀ p, |f p| ≤ 1 := abs_originalInputClassBoundaryWeight_le_one
    hη hηnonneg hηone R C
  have hzero (p : LegalMarkedPhysicalPoint q)
      (hp : p.1 ∉ haarRootCube (Fin q) (R + 1)) : f p = 0 := by
    unfold f originalInputClassBoundaryWeight
    rw [originalInputBoundaryWeight_eq_zero_off_shell hηone hηsupport hR p.1
      (fun hs ↦ hp hs.1), zero_mul]
  obtain ⟨S, hS, hRS, hlaw⟩ :=
    M.map_fullInput_signedIntegral_eq_originalPoisson isCompact_Icc hf hzero c (R + 1)
  let U := haarRootCube (Fin q) S
  let μ := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have hUfin : volume U ≠ ∞ := isCompact_Icc.measure_ne_top
  have hUpos : volume U ≠ 0 := by
    dsimp only [U]
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  have : IsProbabilityMeasure μ := normalizedFiniteLaw_probability _ hmass
  let r := (volume U).toNNReal
  let P := blockDataLaw (μ.prod α) (fun n ↦ poissonMeasure r {n})
  let Q := blockDataLaw (μ.prod β) (fun n ↦ poissonMeasure r {n})
  let B := blockDataLaw (μ.prod γ) (fun n ↦ poissonMeasure r {n})
  have : IsProbabilityMeasure P := originalActualBoundary_blockLaw_probability _ _
  have : IsProbabilityMeasure Q := originalActualBoundary_blockLaw_probability _ _
  have hB : Measurable (legalInputBlockTest f) := measurable_legalInputBlockTest hf
  have hI : Measurable I := measurable_originalActualInputBoundaryReadout hηm R hC c
  have hmap : (M.law : Measure (LegalMarkedOptimalInputScene q)).map I =
      B.map (legalInputBlockTest f) := by
    rw [hlaw]
    by_cases hc : c = 0
    · change (P.prod Q).map (fun b ↦ legalInputBlockTest f
        (if c = 0 then b.1 else b.2)) = B.map (legalInputBlockTest f)
      have heq : B = P := by simp only [B, P, γ, hc, ↓reduceIte]
      rw [heq]
      simp only [hc, ↓reduceIte]
      rw [show (fun b ↦ legalInputBlockTest f b.1) = legalInputBlockTest f ∘ Prod.fst from rfl,
        ← Measure.map_map hB measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    · change (P.prod Q).map (fun b ↦ legalInputBlockTest f
        (if c = 0 then b.1 else b.2)) = B.map (legalInputBlockTest f)
      have heq : B = Q := by simp only [B, Q, γ, hc, ↓reduceIte]
      rw [heq]
      simp only [hc, ↓reduceIte]
      rw [show (fun b ↦ legalInputBlockTest f b.2) = legalInputBlockTest f ∘ Prod.snd from rfl,
        ← Measure.map_map hB measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  have hread (Φ : ℝ → ℝ) (hΦ : Measurable Φ) :
      (∫ s, Φ (I s) ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ b, Φ (legalInputBlockTest f b) ∂B := by
    rw [← integral_map hI.aemeasurable hΦ.aestronglyMeasurable, hmap,
      integral_map hB.aemeasurable hΦ.aestronglyMeasurable]
  have hL2 : MemLp I 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
    have hblock := memLp_two_originalPoisson_blockTest (μ.prod γ) r hf hb
    have hmapL2 : MemLp id 2 (B.map (legalInputBlockTest f)) :=
      (memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable hB.aemeasurable).mpr hblock
    rw [← hmap] at hmapL2
    exact (memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable hI.aemeasurable).mp
      hmapL2
  have hzeroS (p : LegalMarkedPhysicalPoint q) (hp : p.1 ∉ U) : f p = 0 := by
    apply hzero
    intro hx
    apply hp
    exact (mem_haarRootCube_iff_norm_le hS.le p.1).mpr
      (((mem_haarRootCube_iff_norm_le (by linarith) p.1).mp hx).trans hRS)
  have hphysicalMean : (∫ p, f p ∂((volume : Measure (Fin q → ℝ)).restrict U).prod γ) = 0 := by
    rw [integral_marked_restrict_spatial_eq_full γ hzeroS,
      ← integral_marked_restrict_spatial_eq_full γ hzero]
    exact integral_originalInputClassBoundaryWeight_eq_zero hη hηone hηsupport hR γ C
  have hphysicalSq : (∫ p, (f p) ^ 2
      ∂((volume : Measure (Fin q → ℝ)).restrict U).prod γ) =
      γ.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 := by
    have hzS (p : LegalMarkedPhysicalPoint q) (hp : p.1 ∉ U) : (f p) ^ 2 = 0 := by
      rw [hzeroS p hp, zero_pow (by decide : 2 ≠ 0)]
    have hz (p : LegalMarkedPhysicalPoint q)
        (hp : p.1 ∉ haarRootCube (Fin q) (R + 1)) : (f p) ^ 2 = 0 := by
      rw [hzero p hp, zero_pow (by decide : 2 ≠ 0)]
    rw [integral_marked_restrict_spatial_eq_full γ hzS,
      ← integral_marked_restrict_spatial_eq_full γ hz]
    exact integral_sq_originalInputClassBoundaryWeight hηone hηsupport hR γ hC
  have hintensity : (r : ℝ≥0∞) • (μ.prod γ) =
      ((volume : Measure (Fin q → ℝ)).restrict U).prod γ := by
    rw [show (r : ℝ≥0∞) = volume U from ENNReal.coe_toNNReal hUfin]
    exact physicalIntensity_smul_normalized_window q hUfin hUpos γ
  have hmean : (r : ℝ) * ∫ p, f p ∂μ.prod γ = 0 := by
    rw [← smul_eq_mul, ← ENNReal.coe_toReal, ← integral_smul_measure, hintensity, hphysicalMean]
  have hsecond := integral_sq_centered_originalPoisson_blockTest (μ.prod γ) r hf zero_le_one hb
  rw [hmean] at hsecond
  simp only [sub_zero] at hsecond
  have hrhs : (r : ℝ) * ∫ p, (f p) ^ 2 ∂μ.prod γ =
      γ.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 := by
    rw [← smul_eq_mul, ← ENNReal.coe_toReal, ← integral_smul_measure, hintensity, hphysicalSq]
  rw [hrhs] at hsecond
  have hactualMean : (∫ s, I s ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) = 0 := by
    calc
      _ = ∫ b, legalInputBlockTest f b ∂B := hread id measurable_id
      _ = 0 := (integral_originalPoisson_blockTest _ _ hf hb).trans hmean
  have hvariance : variance I (M.law : Measure (LegalMarkedOptimalInputScene q)) =
      γ.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 := by
    rw [variance_eq_integral hI.aemeasurable, hactualMean]
    simpa only [sub_zero] using (hread (fun x ↦ x ^ 2) (by fun_prop)).trans hsecond
  refine ⟨hL2, hactualMean, hvariance, ?_⟩
  rw [hvariance]
  apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
  simpa only [Fintype.card_fin] using
    (integral_sq_originalInputBoundaryWeight_le_shell hηm hη hηnonneg hηone hηsupport hR).trans
      (volume_real_originalInputBoundaryShell_le hR)

/-- Each fixed compact spatial window contains only finitely many full original
input points almost surely, even though every original clock mark is retained. -/
theorem LegalWeightedStationaryPoissonMatching.ae_finite_fullSpatialInput
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.2 : Measure (LegalColoredInputPoint q)) ((K ×ˢ univ) ×ˢ univ) < ∞ := by
  obtain ⟨S, hS, _, hlaw⟩ := M.map_fullSpatialInputRestriction_eq_originalPoisson hK 0
  let U : Set (LegalColoredInputPoint q) := (K ×ˢ univ) ×ˢ univ
  have hU : MeasurableSet U := (hK.measurableSet.prod MeasurableSet.univ).prod
    MeasurableSet.univ
  have hr : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simpa only [Measure.restrict_apply hV, Function.comp_def] using
      (Measure.measurable_coe (hV.inter hU)).comp measurable_localFiniteMeasure_coe
  have hl := hr.comp (measurable_snd : Measurable
    (Prod.snd : LegalMarkedOptimalInputScene q → LocalFiniteMeasure (LegalColoredInputPoint q)))
  have hb := hr.comp (measurable_legalInputTwoBlockLocal q)
  have hfiniteSet : MeasurableSet {μ : Measure (LegalColoredInputPoint q) | μ univ < ∞} :=
    measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const
  have hright : ∀ᵐ μ ∂(legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
      (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U), μ univ < ∞ := by
    apply (ae_map_iff hb.aemeasurable hfiniteSet).mpr
    apply Eventually.of_forall
    intro b
    change ((legalInputTwoBlockMeasure q b).restrict U) univ < ∞
    exact measure_lt_top _ _
  rw [← hlaw] at hright
  have hleft := (ae_map_iff hl.aemeasurable hfiniteSet).mp hright
  simpa only [Function.comp_def, Measure.restrict_apply_univ, U] using hleft

/-- The actual full-input boundary integral is almost surely a genuine
integrable signed point sum, with no undefined-integral fallback. -/
theorem LegalWeightedStationaryPoissonMatching.ae_integrable_fullInput_boundaryWeight
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {η : (Fin q → ℝ) → ℝ} (hηm : Measurable η) (hη : Integrable η)
    (hηnonneg : ∀ x, 0 ≤ η x) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable (originalInputClassBoundaryWeight η R C) (legalInputColorMeasure q s.2 c) := by
  let K := haarRootCube (Fin q) (R + 1)
  let B : Set (LegalMarkedPhysicalPoint q) := K ×ˢ univ
  have hB : MeasurableSet B := measurableSet_Icc.prod MeasurableSet.univ
  have hf := measurable_originalInputClassBoundaryWeight hηm R hC
  have hb := abs_originalInputClassBoundaryWeight_le_one hη hηnonneg hηone R C
  filter_upwards [M.ae_finite_fullSpatialInput (K := K) isCompact_Icc] with s hs
  have hcount : legalInputColorMeasure q s.2 c B < ∞ := by
    rw [legalInputColorMeasure, Measure.map_apply measurable_fst hB,
      Measure.restrict_apply (hB.preimage measurable_fst)]
    apply lt_of_le_of_lt (measure_mono _) hs
    exact fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have : IsFiniteMeasure ((legalInputColorMeasure q s.2 c).restrict B) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hcount⟩
  have hi : IntegrableOn (originalInputClassBoundaryWeight η R C) B
      (legalInputColorMeasure q s.2 c) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hb p))
  have hzero (p : LegalMarkedPhysicalPoint q) (hp : p ∉ B) :
      originalInputClassBoundaryWeight η R C p = 0 := by
    have hnot : p.1 ∉ K := fun hx ↦ hp ⟨hx, mem_univ _⟩
    unfold originalInputClassBoundaryWeight
    rw [originalInputBoundaryWeight_eq_zero_off_shell hηone hηsupport hR p.1
      (fun hm ↦ hnot hm.1), zero_mul]
  have heq : B.indicator (originalInputClassBoundaryWeight η R C) =
      originalInputClassBoundaryWeight η R C := by
    funext p
    by_cases hp : p ∈ B <;> simp [hp, hzero p]
  rw [← heq]
  exact (integrable_indicator_iff hB).mpr hi

end OTSelector.Reconstruction
