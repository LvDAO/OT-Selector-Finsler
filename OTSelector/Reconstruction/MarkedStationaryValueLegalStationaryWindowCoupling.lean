import OTSelector.Probability.IndependentJoining
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowLaw

/-!
# Coupling an actual stationary window to its literal original Poisson arrays

Disintegration over the unchanged colored input restriction preserves both
original marginal laws and identifies the window point measures almost surely.
The stationary plan may depend on its inputs arbitrarily. No iid law is assigned
to its selected or unmatched endpoints.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Equal original input readout laws admit a joining preserving both complete
original objects and agreeing on that readout almost surely. -/
theorem exists_joint_original_input_readout
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableEq Z]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : X → Z) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (hlaw : P.map f = Q.map g) :
    ∃ R : ProbabilityMeasure (X × Y),
      (R : Measure (X × Y)).map Prod.fst = P ∧
      (R : Measure (X × Y)).map Prod.snd = Q ∧
      ∀ᵐ p ∂(R : Measure (X × Y)), f p.1 = g p.2 := by
  let ρ : Measure (Z × X) := P.map (fun x ↦ (f x, x))
  let σ : Measure (Z × Y) := Q.map (fun y ↦ (g y, y))
  have hρ : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map (hf.prodMk measurable_id).aemeasurable
  have hσ : IsProbabilityMeasure σ :=
    Measure.isProbabilityMeasure_map (hg.prodMk measurable_id).aemeasurable
  have henv : ρ.fst = σ.fst := by
    exact (Measure.fst_map_prodMk measurable_id).trans
      (hlaw.trans (Measure.fst_map_prodMk measurable_id).symm)
  let J := relativeIndependentJoining ρ σ
  have hl := relativeIndependentJoining_map_left ρ σ
  have hr := relativeIndependentJoining_map_right ρ σ henv
  change J.map (fun p ↦ (p.1, p.2.1)) = ρ at hl
  change J.map (fun p ↦ (p.1, p.2.2)) = σ at hr
  have hρsnd : ρ.map Prod.snd = P := by
    exact (Measure.snd_map_prodMk hf).trans (Measure.map_id)
  have hσsnd : σ.map Prod.snd = Q := by
    exact (Measure.snd_map_prodMk hg).trans (Measure.map_id)
  let R : ProbabilityMeasure (X × Y) :=
    ⟨J.map Prod.snd, Measure.isProbabilityMeasure_map measurable_snd.aemeasurable⟩
  have hlawL : (R : Measure (X × Y)).map Prod.fst = P := by
    change (J.map Prod.snd).map Prod.fst = P
    rw [Measure.map_map measurable_fst measurable_snd]
    have h := congrArg (fun μ : Measure (Z × X) ↦ μ.map Prod.snd) hl
    rw [Measure.map_map measurable_snd (measurable_fst.prodMk measurable_snd.fst)] at h
    simpa only [hρsnd, Function.comp_def] using h
  have hlawR : (R : Measure (X × Y)).map Prod.snd = Q := by
    change (J.map Prod.snd).map Prod.snd = Q
    rw [Measure.map_map measurable_snd measurable_snd]
    have h := congrArg (fun μ : Measure (Z × Y) ↦ μ.map Prod.snd) hr
    rw [Measure.map_map measurable_snd (measurable_fst.prodMk measurable_snd.snd)] at h
    simpa only [hσsnd, Function.comp_def] using h
  have hleft : ∀ᵐ p ∂J, f p.2.1 = p.1 := by
    have h : ∀ᵐ p ∂ρ, f p.2 = p.1 := by
      exact (ae_map_iff (hf.prodMk measurable_id).aemeasurable
        (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst)).mpr (.of_forall fun x ↦ rfl)
    have hmap : ∀ᵐ p ∂J.map (fun p ↦ (p.1, p.2.1)), f p.2 = p.1 := by
      simpa only [hl] using h
    exact ae_of_ae_map (measurable_fst.prodMk measurable_snd.fst).aemeasurable hmap
  have hright : ∀ᵐ p ∂J, g p.2.2 = p.1 := by
    have h : ∀ᵐ p ∂σ, g p.2 = p.1 := by
      exact (ae_map_iff (hg.prodMk measurable_id).aemeasurable
        (measurableSet_eq_fun (hg.comp measurable_snd) measurable_fst)).mpr (.of_forall fun y ↦ rfl)
    have hmap : ∀ᵐ p ∂J.map (fun p ↦ (p.1, p.2.2)), g p.2 = p.1 := by
      simpa only [hr] using h
    exact ae_of_ae_map (measurable_fst.prodMk measurable_snd.snd).aemeasurable hmap
  refine ⟨R, hlawL, hlawR, ?_⟩
  change ∀ᵐ p ∂J.map Prod.snd, f p.1 = g p.2
  apply (ae_map_iff measurable_snd.aemeasurable
    (measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp measurable_snd))).mpr
  filter_upwards [hleft, hright] with p hp hq
  exact hp.trans hq.symm

local instance markedStationaryValueLegalStationaryWindowCouplingInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryWindowCouplingPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- An arbitrary actual scene and literal original finite Poisson arrays
admit a joint law preserving both complete marginals and equating the input
window measures. No assertion is made that the scene plan is full. -/
theorem exists_originalPoisson_windowCoupling_of_laplace
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hLaplace : ∀ S : ℝ, 0 < S →
      ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
      (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
      (∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
          ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0, ∃ R : ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.fst =
        (Q : Measure (LegalMarkedOptimalInputScene q)) ∧
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.snd =
        legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        legalInputRestrictionLocal U p.1.2 =
        legalInputRestrictionLocal U (legalInputTwoBlockLocal q p.2) := by
  have : StandardBorelSpace (MarkedCloudSpace q ℝ) := by infer_instance
  have : Nonempty (LegalMarkedOptimalInputScene q) :=
    nonempty_of_isProbabilityMeasure (Q : Measure (LegalMarkedOptimalInputScene q))
  obtain ⟨S, hS, hlaw⟩ := map_inputRestrictionLocal_eq_originalPoisson_of_laplace Q hLaplace hU
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have : IsProbabilityMeasure (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) :=
    isProbabilityMeasure_legalInputPoissonWindowLaw q hS.le measurableSet_Icc (Subset.refl _) hvol α β
  let L := 4 * (S + 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hmargin : S + 1 < L / 2 := by dsimp [L]; linarith
  have hz : (0 : Fin q → ℝ) ∈ haarRootCube (Fin q) (L / 2 - S - 1) := by
    constructor <;> intro i <;> dsimp <;> linarith
  let P := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))
  let φ : TwoMarkedCloudSpace q ℝ ℝ →
      BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q) :=
    fun ω ↦ legalInputRootWindows q (Real.toNNReal L) (haarRootCube (Fin q) S) (0, ω)
  have hφ : Measurable φ :=
    (measurable_legalInputRootWindows q (Real.toNNReal L) measurableSet_Icc).comp
      measurable_prodMk_left
  have hφlaw : P.map φ = legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
    exact map_legalInputRootWindows_eq_of_inner_root q hS.le hmargin measurableSet_Icc
      (Subset.refl _) hvol α β hz
  let f : LegalMarkedOptimalInputScene q → LocalFiniteMeasure (LegalColoredInputPoint q) :=
    fun s ↦ legalInputRestrictionLocal U s.2
  let g' : (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) →
      LocalFiniteMeasure (LegalColoredInputPoint q) :=
    fun b ↦ legalInputRestrictionLocal U (legalInputTwoBlockLocal q b)
  have hf : Measurable f :=
    (measurable_legalInputRestrictionLocal hU.measurableSet).comp measurable_snd
  have hg : Measurable g' :=
    (measurable_legalInputRestrictionLocal hU.measurableSet).comp
      (measurable_legalInputTwoBlockLocal q)
  have hraw : (Q : Measure _).map f = P.map (g' ∘ φ) := by
    rw [← Measure.map_map hg hφ, hφlaw]
    exact hlaw
  obtain ⟨R₀, hleft, hright, heq⟩ := exists_joint_original_input_readout
    (Q : Measure _) P f (g' ∘ φ) hf (hg.comp hφ) hraw
  let R := R₀.map (measurable_id.prodMap hφ).aemeasurable
  refine ⟨S, hS, R, ?_, ?_, ?_⟩
  · change ((R₀ : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map (Prod.map id φ)).map Prod.fst = _
    rw [Measure.map_map measurable_fst (measurable_id.prodMap hφ)]
    exact hleft
  · change ((R₀ : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map (Prod.map id φ)).map Prod.snd = _
    rw [Measure.map_map measurable_snd (measurable_id.prodMap hφ)]
    rw [show Prod.snd ∘ Prod.map id φ = φ ∘ Prod.snd from rfl,
      ← Measure.map_map hφ measurable_snd, hright, hφlaw]
  · change ∀ᵐ p ∂((R₀ : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map (Prod.map id φ)), f p.1 = g' p.2
    apply (ae_map_iff (measurable_id.prodMap hφ).aemeasurable
      (measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp measurable_snd))).mpr
    exact heq

/-- The actual stationary scene and literal original finite Poisson arrays
can be carried together without changing either complete marginal law. Their
unchanged colored window measures agree almost surely. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalPoisson_windowCoupling
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0, ∃ R : ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.fst =
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.snd =
        legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        legalInputRestrictionLocal U p.1.2 =
        legalInputRestrictionLocal U (legalInputTwoBlockLocal q p.2) := by
  exact exists_originalPoisson_windowCoupling_of_laplace M.law M.input_laplace hU

end OTSelector.Reconstruction
