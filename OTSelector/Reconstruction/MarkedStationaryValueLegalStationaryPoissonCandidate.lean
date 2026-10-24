import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCountingMatching
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputForwardScene
import OTSelector.Reconstruction.MarkedStationaryValueLegalSignedPalmLimit

/-!
# Actual legal pressure produces a full stationary Poisson matching

The same original canonical finite optima produce a genuine integer matching
of every unchanged original Poisson input atom. Its true full-displacement
Palm is a probability, has the original scalar marginals, and has both finite
weighted energy and a finite displacement second moment. Its signed value is
at most the actual legal finite-pressure limit. The original finite-cloud weak
provenance is retained alongside the candidate.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

local instance markedStationaryValueLegalStationaryPoissonCandidateInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryPoissonCandidatePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual q-dimensional source-anchored Palm, retaining both original
clocks and the complete original transverse displacement. -/
def legalMarkedJointPalm (q : ℕ) (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    Measure (PhysicalPairPalmMark (Fin q)) :=
  cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))

/-- A weighted finite-energy stationary integer matching with the prescribed
original independent Poisson inputs. The input law is specified by its full
compact Laplace functional, which determines the whole random-measure law. -/
structure LegalWeightedStationaryPoissonMatching (q : ℕ) (α β : Measure ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) where
  law : ProbabilityMeasure (LegalMarkedOptimalInputScene q)
  stationary : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
    (law : Measure (LegalMarkedOptimalInputScene q)) (law : Measure (LegalMarkedOptimalInputScene q))
  full_matching : ∀ᵐ s ∂(law : Measure (LegalMarkedOptimalInputScene q)), IsFullOriginalInputMatching q s
  forward : ∀ᵐ s ∂(law : Measure (LegalMarkedOptimalInputScene q)),
    ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2
  input_laplace : ∀ S : ℝ, 0 < S → ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
    (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
      x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
    (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(law : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β
  palm_probability : IsProbabilityMeasure (legalMarkedJointPalm q law)
  source_clock : (legalMarkedJointPalm q law).map (fun m ↦ m.1.1) = α
  target_clock : (legalMarkedJointPalm q law).map (fun m ↦ m.1.2) = β
  kinetic_integrable : Integrable (fun m ↦ kin m.1.1 m.1.2 m.2) (legalMarkedJointPalm q law)
  probe_integrable : Integrable (fun m ↦ g m.1.1 m.1.2) (legalMarkedJointPalm q law)

/-- Original kinetic energy plus the original paired-clock probe tilt, under
the same actual source-anchored probability Palm. -/
def LegalWeightedStationaryPoissonMatching.value {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ) : ℝ :=
  (∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q M.law) +
    t * ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q M.law

/-- All matching, prescribed-input, stationarity, probability-Palm and finite
second-moment assertions are produced from the original data. The candidate
is the actual canonical finite-optimum limit, and its signed value is at most
the actual legal Poisson pressure. -/
theorem FiniteScalarBins.exists_legalWeightedStationaryPoissonMatching_energy_le
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
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (hgc : ContinuousOn (Function.uncurry g) K) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure q id id α β kin g R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p ∧
      ∀ t : ℝ, ∃ M : LegalWeightedStationaryPoissonMatching q α β kin g,
        Integrable (fun m ↦ ‖m.2‖ ^ 2) (legalMarkedJointPalm q M.law) ∧ M.value t ≤ p t ∧
        ∃ (L : ℕ → ℝ) (hL : ∀ k, 0 < L k), Tendsto L atTop atTop ∧
          Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
            (L k) (hL k)) atTop (𝓝 M.law) := by
  obtain ⟨p, hp, hc, hl, hscene⟩ := D.exists_stationary_fullInput_cubePalm_signed_energy_le
    hδ hIm π α β hπ hI hgap hsep q hq hC hG hk hkn hkb hhom hg hgb
    hA hB hα hβ hK matrix hmatrix hpos hlegal hactual hgc
  refine ⟨p, hp, hc, hl, fun t ↦ ?_⟩
  obtain ⟨L, hL, hlarge, Q, φ, hφ, hw, hstat, hfull, hPalm, hgapPalm, henergy, hinput⟩ := hscene t
  have hq0 : 0 < q := by omega
  have hlargeφ := hlarge.comp hφ.tendsto_atTop
  have hmatching := ae_isFullOriginalInputMatching_of_legalMarkedInputSceneLaw_tendsto
    q hq0 α β kin hk g hg t (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hlargeφ hw hfull
  have hforward : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
    filter_upwards [ae_support_clockGap_of_legalMarkedInputSceneLaw_tendsto
      q hq0 α β kin hk g hg t (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hw hsep] with s hs
    intro e he
    have h := hs e he
    linarith
  let M : LegalWeightedStationaryPoissonMatching q α β kin g :=
    { law := Q
      stationary := hstat
      full_matching := hmatching
      forward := hforward
      input_laplace := hinput
      palm_probability := hPalm.1
      source_clock := hPalm.2.1
      target_clock := hPalm.2.2
      kinetic_integrable := henergy.1
      probe_integrable := henergy.2.1 }
  exact ⟨M, henergy.2.2.1, henergy.2.2.2,
    (fun k ↦ L (φ k)), (fun k ↦ hL (φ k)), hlargeφ, hw⟩

end OTSelector.Reconstruction
