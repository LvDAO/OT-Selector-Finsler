import OTSelector.Reconstruction.OriginalPoissonHilbertInputMoments
import OTSelector.Reconstruction.OriginalActualInputBoundaryLawTransfer

/-! Hilbert readouts retain the same actual stationary scene's entire original Poisson law. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

local instance poissonHilbertActualInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance poissonHilbertActualPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

omit [CompleteSpace H] in
private theorem measurable_hilbertIntegral_of_measurable {X : Type*} [MeasurableSpace X]
    {F : X → H} (hF : Measurable F) :
    Measurable (fun μ : Measure X ↦ ∫ x, F x ∂μ) := by
  let κ : Kernel (Measure X) X := ⟨id, measurable_id⟩
  exact (hF.stronglyMeasurable.integral_kernel (κ := κ)).measurable

omit [CompleteSpace H] in
private theorem originalInputColor_hilbertIntegral_eq_colored {q : ℕ}
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2)
    {F : LegalMarkedPhysicalPoint q → H} (hF : Measurable F) :
    (∫ x, F x ∂legalInputColorMeasure q μ c) =
      ∫ x, {p : LegalColoredInputPoint q | p.2 = c}.indicator (fun p ↦ F p.1) x
        ∂(μ : Measure (LegalColoredInputPoint q)) := by
  rw [legalInputColorMeasure, integral_map measurable_fst.aemeasurable
    hF.aestronglyMeasurable]
  exact (integral_indicator (s := {p : LegalColoredInputPoint q | p.2 = c})
    (μ := (μ : Measure (LegalColoredInputPoint q)))
    (measurable_snd (measurableSet_singleton c))).symm

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
private theorem integral_legalInputTwoBlockMeasure_hilbert (q : ℕ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (F : LegalColoredInputPoint q → H) :
    (∫ x, F x ∂legalInputTwoBlockMeasure q b) =
      originalPoissonHilbertBlockTest (fun x ↦ F (x, 0)) b.1+
        originalPoissonHilbertBlockTest (fun x ↦ F (x, 1)) b.2 := by
  have hi (d : BlockData (LegalColoredInputPoint q)) :
      Integrable F (legalInputBlockMeasure d) := by
    unfold legalInputBlockMeasure
    exact integrable_finsetSum_measure.mpr (fun i _ ↦ integrable_dirac (by simp))
  rw [legalInputTwoBlockMeasure, integral_add_measure (hi _) (hi _),
    integral_legalInputBlockMeasure_hilbert, integral_legalInputBlockMeasure_hilbert]
  rfl

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
private theorem originalInputTwoBlock_color_hilbertIntegral {q : ℕ} (c : Fin 2)
    (F : LegalMarkedPhysicalPoint q → H)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    (∫ x, {p : LegalColoredInputPoint q | p.2 = c}.indicator (fun p ↦ F p.1) x
      ∂legalInputTwoBlockMeasure q b) =
      originalPoissonHilbertBlockTest F (if c = 0 then b.1 else b.2) := by
  rw [integral_legalInputTwoBlockMeasure_hilbert]
  fin_cases c <;> simp [originalPoissonHilbertBlockTest]

/-- Any measurable Hilbert response with compact spatial support retains the
complete original finite-Poisson law on the same actual stationary scene. -/
theorem LegalWeightedStationaryPoissonMatching.map_fullInput_hilbertIntegral_eq_originalPoisson
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    {F : LegalMarkedPhysicalPoint q → H} (hF : Measurable F)
    (hsupport : ∀ p, p.1 ∉ K → F p = 0) (c : Fin 2) (Rmin : ℝ) :
    ∃ S > 0, Rmin ≤ S ∧
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ ∫ p, F p ∂legalInputColorMeasure q s.2 c) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ originalPoissonHilbertBlockTest F (if c = 0 then b.1 else b.2)) := by
  obtain ⟨S, hS, hRS, hlaw⟩ := M.map_fullSpatialInputRestriction_eq_originalPoisson hK Rmin
  let U : Set (LegalColoredInputPoint q) := (K ×ˢ univ) ×ˢ univ
  have hU : MeasurableSet U := (hK.measurableSet.prod MeasurableSet.univ).prod
    MeasurableSet.univ
  let Ft := {p : LegalColoredInputPoint q | p.2 = c}.indicator (fun p ↦ F p.1)
  have hFt : Measurable Ft := (hF.comp measurable_fst).indicator
    (measurable_snd (measurableSet_singleton c))
  let read : Measure (LegalColoredInputPoint q) → H := fun μ ↦ ∫ p, Ft p ∂μ
  have hr : Measurable read := measurable_hilbertIntegral_of_measurable hFt
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
  have hzero (x : LegalColoredInputPoint q) (hx : x ∉ U) : Ft x = 0 := by
    have hnot : x.1.1 ∉ K := fun h ↦ hx ⟨⟨h, mem_univ _⟩, mem_univ _⟩
    by_cases hc : x.2 = c <;> simp [Ft, hc, hsupport x.1 hnot]
  have hread (μ : Measure (LegalColoredInputPoint q)) : read (μ.restrict U) = ∫ p, Ft p ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have he := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦ P.map read) hlaw
  rw [Measure.map_map hr hleft, Measure.map_map hr hright] at he
  refine ⟨S, hS, hRS, ?_⟩
  simpa only [Function.comp_def, hread, Ft,
    originalInputColor_hilbertIntegral_eq_colored _ c hF,
    originalInputTwoBlock_color_hilbertIntegral] using he


private theorem originalPoissonHilbert_blockLaw_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    IsProbabilityMeasure (blockDataLaw ν (fun n ↦ poissonMeasure r {n})) := by
  rw [blockDataLaw_eq_map_cloud]
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_sigma_mk n).comp
    (measurable_pi_lambda _ (fun j : Fin n ↦ measurable_pi_apply (j : ℕ)))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Every bounded compact-spatial Hilbert response is genuinely integrable
against the same actual input measure almost surely. -/
theorem LegalWeightedStationaryPoissonMatching.ae_integrable_fullInput_hilbertResponse
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    {F : LegalMarkedPhysicalPoint q → H} (hF : Measurable F)
    (hsupport : ∀ p, p.1 ∉ K → F p = 0) {B : ℝ} (hbound : ∀ p, ‖F p‖ ≤ B)
    (c : Fin 2) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable F (legalInputColorMeasure q s.2 c) := by
  let W : Set (LegalMarkedPhysicalPoint q) := K ×ˢ univ
  have hW : MeasurableSet W := hK.measurableSet.prod MeasurableSet.univ
  filter_upwards [M.ae_finite_fullSpatialInput hK] with s hs
  have hfinite : legalInputColorMeasure q s.2 c W < ∞ := by
    rw [legalInputColorMeasure, Measure.map_apply measurable_fst hW,
      Measure.restrict_apply (hW.preimage measurable_fst)]
    exact lt_of_le_of_lt (measure_mono (by
      intro p hp
      exact ⟨hp.1, mem_univ _⟩)) hs
  have : IsFiniteMeasure ((legalInputColorMeasure q s.2 c).restrict W) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  have hi : IntegrableOn F W (legalInputColorMeasure q s.2 c) :=
    Integrable.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall hbound)
  have heq : W.indicator F = F := by
    funext p
    by_cases hp : p ∈ W
    · exact indicator_of_mem hp F
    · rw [indicator_of_notMem hp, hsupport p (by simpa only [W, mem_prod, mem_univ, and_true] using hp)]
  simpa only [heq] using (integrable_indicator_iff hW).mpr hi

/-- The actual stationary original input has the exact centered Hilbert Poisson
variance on its own unchanged scene law. All original marks and the given color remain. -/
theorem LegalWeightedStationaryPoissonMatching.centered_fullInput_hilbert_moments
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {N : Type*} [Countable N] (b : HilbertBasis N ℝ H)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    {F : LegalMarkedPhysicalPoint q → H} (hF : Measurable F)
    (hsupport : ∀ p, p.1 ∉ K → F p = 0) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ p, ‖F p‖ ≤ B) (c : Fin 2) :
    let γ := if c = 0 then α else β
    let intensity := (volume : Measure (Fin q → ℝ)).prod γ
    let m := ∫ p, F p ∂intensity
    let I := fun s : LegalMarkedOptimalInputScene q ↦ ∫ p, F p ∂legalInputColorMeasure q s.2 c
    (∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable F (legalInputColorMeasure q s.2 c)) ∧
    MemLp (fun s ↦ I s-m) 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, I s ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) = m ∧
    (∫ s, ‖I s-m‖^2 ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ p, ‖F p‖^2 ∂intensity := by
  dsimp only
  let γ := if c = 0 then α else β
  have : IsProbabilityMeasure γ := by
    by_cases hc : c = 0 <;> simp only [γ, hc, ↓reduceIte] <;> infer_instance
  let intensity := (volume : Measure (Fin q → ℝ)).prod γ
  let m := ∫ p, F p ∂intensity
  let I := fun s : LegalMarkedOptimalInputScene q ↦ ∫ p, F p ∂legalInputColorMeasure q s.2 c
  obtain ⟨R₀, hR₀, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  obtain ⟨S, hS, hRS, hlaw⟩ := M.map_fullInput_hilbertIntegral_eq_originalPoisson
    hK hF hsupport c R₀
  let U := haarRootCube (Fin q) S
  let μ := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have hUfin : volume U ≠ ∞ := isCompact_Icc.measure_ne_top
  have hUpos : volume U ≠ 0 := by
    dsimp only [U]
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2*S) q)).ne'
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  have : IsProbabilityMeasure μ := normalizedFiniteLaw_probability _ hmass
  let r := (volume U).toNNReal
  let P := blockDataLaw (μ.prod α) (fun n ↦ poissonMeasure r {n})
  let Q := blockDataLaw (μ.prod β) (fun n ↦ poissonMeasure r {n})
  let Pb := blockDataLaw (μ.prod γ) (fun n ↦ poissonMeasure r {n})
  have : IsProbabilityMeasure P := originalPoissonHilbert_blockLaw_probability _ _
  have : IsProbabilityMeasure Q := originalPoissonHilbert_blockLaw_probability _ _
  have hblock : Measurable (originalPoissonHilbertBlockTest F) :=
    measurable_originalPoissonHilbertBlockTest hF
  have hI : Measurable I := by
    have hm := hF.stronglyMeasurable.integral_kernel (κ := legalMarkedInputColorKernel q c)
    simpa only [I, legalMarkedInputColorKernel_apply] using hm.measurable
  have hmap : (M.law : Measure (LegalMarkedOptimalInputScene q)).map I =
      Pb.map (originalPoissonHilbertBlockTest F) := by
    rw [hlaw]
    by_cases hc : c = 0
    · change (P.prod Q).map (fun z ↦ originalPoissonHilbertBlockTest F
        (if c = 0 then z.1 else z.2)) = Pb.map (originalPoissonHilbertBlockTest F)
      have heq : Pb = P := by simp only [Pb, P, γ, hc, ↓reduceIte]
      rw [heq]
      simp only [hc, ↓reduceIte]
      rw [show (fun z ↦ originalPoissonHilbertBlockTest F z.1) =
        originalPoissonHilbertBlockTest F ∘ Prod.fst from rfl,
        ← Measure.map_map hblock measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    · change (P.prod Q).map (fun z ↦ originalPoissonHilbertBlockTest F
        (if c = 0 then z.1 else z.2)) = Pb.map (originalPoissonHilbertBlockTest F)
      have heq : Pb = Q := by simp only [Pb, Q, γ, hc, ↓reduceIte]
      rw [heq]
      simp only [hc, ↓reduceIte]
      rw [show (fun z ↦ originalPoissonHilbertBlockTest F z.2) =
        originalPoissonHilbertBlockTest F ∘ Prod.snd from rfl,
        ← Measure.map_map hblock measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  have hzero (p : LegalMarkedPhysicalPoint q) (hp : p.1 ∉ U) : F p = 0 := by
    apply hsupport p
    intro hpK
    exact hp ((mem_haarRootCube_iff_norm_le hS.le p.1).mpr ((hKR p.1 hpK).le.trans hRS))
  let windowIntensity := ((volume : Measure (Fin q → ℝ)).restrict U).prod γ
  have hrestr : windowIntensity = intensity.restrict (U ×ˢ univ) := by
    simpa only [windowIntensity, intensity, Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure (Fin q → ℝ))) (ν := γ) U univ)
  have hmean : (∫ p, F p ∂windowIntensity) = m := by
    rw [hrestr]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    exact hzero p (fun hx ↦ hp ⟨hx, mem_univ _⟩)
  have hsq : (∫ p, ‖F p‖^2 ∂windowIntensity) = ∫ p, ‖F p‖^2 ∂intensity := by
    rw [hrestr]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [hzero p (fun hx ↦ hp ⟨hx, mem_univ _⟩), norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hexact : (r : ℝ≥0∞) • (μ.prod γ) = windowIntensity := by
    dsimp only [r]
    rw [ENNReal.coe_toNNReal hUfin]
    exact physicalIntensity_smul_normalized_window q hUfin hUpos γ
  have hm : (r : ℝ) • (∫ p, F p ∂μ.prod γ) = m := by
    rw [← hmean, ← hexact, integral_smul_measure, ENNReal.coe_toReal]
  obtain ⟨hLp, hvar⟩ := centered_originalPoissonHilbertBlockTest_moments b (μ.prod γ) r hF hB hbound
  rw [hm] at hLp hvar
  have hvar' : (∫ z, ‖originalPoissonHilbertBlockTest F z-m‖^2 ∂Pb) =
      ∫ p, ‖F p‖^2 ∂intensity := by
    rw [hvar, ← smul_eq_mul, ← ENNReal.coe_toReal, ← integral_smul_measure, hexact, hsq]
  refine ⟨M.ae_integrable_fullInput_hilbertResponse hK hF hsupport hbound c, ?_, ?_, ?_⟩
  · have hmapLp : MemLp (fun v : H ↦ v-m) 2 (Pb.map (originalPoissonHilbertBlockTest F)) :=
      (memLp_map_measure_iff (by fun_prop : AEStronglyMeasurable (fun v : H ↦ v-m) _)
        hblock.aemeasurable).mpr hLp
    rw [← hmap] at hmapLp
    exact (memLp_map_measure_iff (by fun_prop : AEStronglyMeasurable (fun v : H ↦ v-m) _)
      hI.aemeasurable).mp hmapLp
  · change (∫ s, id (I s) ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) = m
    rw [← integral_map hI.aemeasurable stronglyMeasurable_id.aestronglyMeasurable, hmap,
      integral_map hblock.aemeasurable stronglyMeasurable_id.aestronglyMeasurable]
    exact (integral_originalPoissonHilbertBlockTest (μ.prod γ) r hF hbound).trans hm
  · rw [← integral_map hI.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun v : H ↦ ‖v-m‖^2) _), hmap,
      integral_map hblock.aemeasurable
        (by fun_prop : AEStronglyMeasurable (fun v : H ↦ ‖v-m‖^2) _)]
    exact hvar'

end OTSelector.Reconstruction
