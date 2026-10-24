import OTSelector.Reconstruction.MarkedStationaryValueLegalInputPalmNormalization

/-!
# The actual original legal pressure produces a legal probability Palm

The original paired clock population supplies the finite pressure limit and
both endpoint deficits. Actual compact positive coefficients remove nonproper
escape. A common weak subsequence of the canonical original legal optima and
their immutable input colors therefore uses every original source and target.
Its true q-dimensional full-displacement Palm is normalized internally and has
both exact original scalar-clock marginals and the positive legal gap. The
prescribed independent Poisson input is retained in its exact compact
Laplace functional, with no independent input coupling supplied afterwards.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInputPalmLimitInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputPalmLimitPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Original separated scalar populations and their actual compact positive
quadratic coefficient produce both the real-scale legal pressure and its own
jointly stationary full-input weak scenes and their original probability Palm.
Every auxiliary compactness, error,
escape and marginal-finiteness input is proved from the original data. -/
theorem FiniteScalarBins.exists_stationary_fullInput_probability_cubePalm
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ) (hIm : MeasurableSet I)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ z ∂π, z.1 ∈ I ∧ z.2 ∈ I) (hgap : ∀ᵐ z ∂π, δ ≤ z.2 - z.1)
    (hsep : ∀ᵐ z ∂α.prod β, δ ≤ |z.2 - z.1|)
    (q : ℕ) (hq : 4 < q)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ ↦ kin z.1 z.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure q id id α β kin g R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p ∧
      ∀ t : ℝ, ∃ (L : ℕ → ℝ) (hL : ∀ k, 0 < L k), Tendsto L atTop atTop ∧
        ∃ Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q), ∃ φ : ℕ → ℕ,
          StrictMono φ ∧ Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
            (L (φ k)) (hL (φ k))) atTop (𝓝 Q) ∧
          (∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
            (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q))) ∧
          (∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
            (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 ∧
              (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1) ∧
          (IsProbabilityMeasure (cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
            Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) ∧
          (cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
            Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))).map
              (fun m ↦ m.1.1) = α ∧
          (cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
            Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))).map
              (fun m ↦ m.1.2) = β) ∧
          (∀ᵐ m ∂cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
            Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))),
              δ ≤ m.1.2 - m.1.1) ∧
          (∀ (S : ℝ), 0 < S → ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
            (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
              x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
            (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
              ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
                ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) := by
  obtain ⟨p, hp, hc, hl, hscene⟩ := D.exists_stationary_fullInput_legalMarkedPressure_limit hδ hIm
    π α β hπ hI hgap hsep q hq hC hG hk hkn hkb hhom hg hgb
    hA hB hα hβ hK matrix hmatrix hpos hlegal hactual
  refine ⟨p, hp, hc, hl, fun t ↦ ?_⟩
  obtain ⟨L, hL, hlarge, Q, φ, hφ, hw, hstat, hfull, hinput⟩ := hscene t
  refine ⟨L, hL, hlarge, Q, φ, hφ, hw, hstat, hfull, ?_, ?_, hinput⟩
  · exact probability_cubePalm_of_legalMarkedInputSceneLaw_tendsto q α β kin hk g hg t
      (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) (hlarge.comp hφ.tendsto_atTop) hw hstat hfull
  · exact ae_cubePalm_legalMarkedInputPairLaw_clockGap q (by omega) α β kin hk g hg t
      (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hw hsep

end OTSelector.Reconstruction
