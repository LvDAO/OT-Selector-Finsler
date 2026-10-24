import OTSelector.Reconstruction.MarkedStationaryValueLegalFocalMarginals
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureLimit

/-!
# Actual stationary full-input scenes with focal endpoint degeneration

The original scalar-bin population produces the real legal pressure limit and
its own canonical optimum subsequence. Interior coefficient positivity and null
endpoint mass, rather than positivity on the whole closed clock support,
recover both full original input marginals of that same stationary joint scene.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalFocalFullSceneInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalFocalFullScenePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Original separated scalar populations and their actual compact positive
quadratic coefficient produce both the real-scale legal pressure and its own
jointly stationary full-input weak scenes. Every auxiliary compactness, error,
escape and marginal-finiteness input is proved from the original data. -/
theorem FiniteScalarBins.exists_stationary_fullInput_legalMarkedPressure_limit_of_interior
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
    {J A₀ B₀ : Set ℝ} (hJ : MeasurableSet J)
    (hA₀ : MeasurableSet A₀) (hB₀ : MeasurableSet B₀)
    (hαJ : α Jᶜ = 0) (hβJ : β Jᶜ = 0)
    (hαA : α A₀ᶜ = 0) (hβB : β B₀ᶜ = 0)
    (hsepAll : ∀ a ∈ A₀, ∀ b ∈ B₀, δ ≤ |b - a|)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix {p | p.1 ∈ J ∧ p.2 ∈ J ∧ p.1 < p.2})
    (hpos : ∀ p, p.1 ∈ J → p.2 ∈ J → p.1 < p.2 → (matrix p).PosDef)
    (hactual : ∀ a ∈ J ∩ A₀, ∀ b ∈ J ∩ B₀, a < b → ∀ v,
      kin a b v = matrixQuadratic (matrix (a, b)) v) :
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
          (∀ (S : ℝ), 0 < S → ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
            (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
              x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
            (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
              ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
                ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) := by
  obtain ⟨p, hp, hc, hl⟩ := exists_legalMarkedScalePressure_limit_of_scalarBins D hδ hIm
    id id measurable_id measurable_id π α β hπ hI hgap hsep q hq
    hC hG hk hkn hkb hhom hg hgb
  refine ⟨p, hp, hc, hl, fun t ↦ ?_⟩
  let L (k : ℕ) : ℝ := (k : ℝ) + 1
  have hL (k : ℕ) : 0 < L k := by dsimp [L]; positivity
  have hlarge : Tendsto L atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨Q, φ, hφ, hw, hstat, hinput⟩ :=
    exists_stationary_originalPoisson_legalMarkedOptimalInputSceneLaw q α β kin hk g hg t L hL hlarge
  refine ⟨L, hL, hlarge, Q, φ, hφ, hw, hstat, ?_, hinput⟩
  have hq0 : 0 < q := by omega
  have hdef := scalarBins_legalMarkedSourceDefect_div_tendsto_zero D hδ π α β hπ hI hgap q hq0
  exact (ae_legalMarkedInput_source_marginal_eq_of_sourceDefect_of_interior q hq0 α β hdef
    hC hG hk hkn hkb hhom hg hgb t (p t) (hp t)
    hJ hA₀ hB₀ hαJ hβJ hαA hβB hδ hsepAll matrix hmatrix hpos hactual
    (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) (hlarge.comp hφ.tendsto_atTop) hw).and
    (ae_legalMarkedInput_target_marginal_eq_of_sourceDefect_of_interior q hq0 α β hdef
      hC hG hk hkn hkb hhom hg hgb t (p t) (hp t)
      hJ hA₀ hB₀ hαJ hβJ hαA hβB hδ hsepAll matrix hmatrix hpos hactual
      (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) (hlarge.comp hφ.tendsto_atTop) hw)

end OTSelector.Reconstruction
