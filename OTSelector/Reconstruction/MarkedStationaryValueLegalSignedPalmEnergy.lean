import OTSelector.Reconstruction.MarkedStationaryValueLegalAllowedEnergyPalm

/-!
# The same actual legal probability Palm has signed energy at most pressure

The original clock marginals and positive forward gap identify the real closed
coefficient carrier. The probability Palm removes the nonnegative shift from
the proved weak energy estimate; kinetic and probe integrability are produced
rather than supplied as candidate admissibility assumptions.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalSignedPalmEnergyInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalSignedPalmEnergyPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Exact original clock marginals and the actual positive forward support
place the full-displacement Palm in the original coefficient carrier. -/
theorem ae_pair_clockCarrier_of_original_marginals
    (q : ℕ) (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (α β : Measure ℝ)
    (hsource : μ.map (fun m ↦ m.1.1) = α) (htarget : μ.map (fun m ↦ m.1.2) = β)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ m ∂μ, δ ≤ m.1.2 - m.1.1)
    {K : Set (ℝ × ℝ)} (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K) :
    ∀ᵐ m ∂μ, m.1 ∈ K := by
  have hαae : ∀ᵐ a ∂α, a ∈ A := ae_iff.mpr hα
  have hβae : ∀ᵐ b ∂β, b ∈ B := ae_iff.mpr hβ
  rw [← hsource] at hαae
  rw [← htarget] at hβae
  have hs : ∀ᵐ m ∂μ, m.1.1 ∈ A := (ae_map_iff measurable_fst.fst.aemeasurable hA).mp hαae
  have ht : ∀ᵐ m ∂μ, m.1.2 ∈ B := (ae_map_iff measurable_fst.snd.aemeasurable hB).mp hβae
  filter_upwards [hs, ht, hgap] with m hmS hmT hmGap
  exact hlegal m.1.1 hmS m.1.2 hmT (by linarith)

/-- The true original joint optimal weak scene has integrable original kinetic
and probe readouts, and its own actual legal probability Palm has signed value
at most the actual legal pressure limit. Coefficients and probes need continuity
only on their original closed legal carrier. -/
theorem integrable_signed_cubePalm_le_legalMarkedPressure_limit
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t p : ℝ)
    (hp : Tendsto (fun R ↦ legalMarkedScalePressure q id id α β kin g R t) atTop (𝓝 p))
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hmatrix : ContinuousOn matrix K)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (hgc : ContinuousOn (Function.uncurry g) K)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ᵐ z ∂α.prod β, δ ≤ |z.2 - z.1|)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    (hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)))
    (hfull : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1) :
    let μ := cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))
    Integrable (fun m ↦ kin m.1.1 m.1.2 m.2) μ ∧
      Integrable (fun m ↦ g m.1.1 m.1.2) μ ∧
        (∫ m, kin m.1.1 m.1.2 m.2 ∂μ) + t * (∫ m, g m.1.1 m.1.2 ∂μ) ≤ p := by
  dsimp only
  let μ := cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))
  have hprob := probability_cubePalm_of_legalMarkedInputSceneLaw_tendsto q α β kin hk g hg t
    L hL hlarge hweak hstat hfull
  have : IsProbabilityMeasure μ := hprob.1
  have hμK : ∀ᵐ m ∂μ, m.1 ∈ K := ae_pair_clockCarrier_of_original_marginals q μ α β
    hprob.2.1 hprob.2.2 hA hB hα hβ hδ
    (ae_cubePalm_legalMarkedInputPairLaw_clockGap q hq α β kin hk g hg t L hL hweak hsep) hlegal
  obtain ⟨F, hFn, hF⟩ := exists_continuous_nonnegative_legal_shifted_energy q hK matrix hmatrix hkn
    hactual hgc (fun w _ ↦ hgb w.1 w.2) t
  have hbound := lintegral_cubePalm_legalMarkedInputPairLaw_continuous_shifted_le q hq α β hC hG hk
    hkn hkb hhom hg hgb t p hp hA hB hα hβ hlegal F hFn hF L hL hlarge hweak
  have hFI : Integrable F μ := ⟨F.continuous.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (.of_forall hFn)).mpr (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  have hlow : -(|t| * G) ≤ p := by
    apply ge_of_tendsto hp
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact legalMarkedScalePressure_lower_bound q measurable_id measurable_id α β hC hG hk hkn hkb hg hgb t hR
  have hFmean : (∫ m, F m ∂μ) ≤ p + |t| * G := by
    rw [← ofReal_integral_eq_lintegral_ofReal hFI (.of_forall hFn)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ p + |t| * G)).mp hbound
  let cost (m : PhysicalPairPalmMark (Fin q)) := kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
  have heq : (fun m ↦ F m - |t| * G) =ᵐ[μ] cost := hμK.mono (fun m hm ↦ by
    change F m - |t| * G = cost m
    rw [hF m hm]
    dsimp [cost]
    ring)
  have hcostI : Integrable cost μ := (hFI.sub (integrable_const _)).congr heq
  have hcostmean : (∫ m, cost m ∂μ) ≤ p := by
    calc
      _ = ∫ m, F m - |t| * G ∂μ := (integral_congr_ae heq).symm
      _ = (∫ m, F m ∂μ) - |t| * G := by rw [integral_sub hFI (integrable_const _)]; simp
      _ ≤ p := by linarith
  have hgI : Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ g m.1.1 m.1.2) μ :=
    Integrable.of_bound (hg.comp (measurable_fst.fst.prodMk measurable_fst.snd)).aestronglyMeasurable
      G (.of_forall (fun m ↦ by simpa only [Real.norm_eq_abs] using hgb m.1.1 m.1.2))
  have hkI : Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ kin m.1.1 m.1.2 m.2) μ :=
    (hcostI.sub (hgI.const_mul t)).congr (.of_forall (fun m ↦ by dsimp [cost]; ring))
  refine ⟨hkI, hgI, ?_⟩
  change (∫ m, kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 ∂μ) ≤ p at hcostmean
  rwa [integral_add hkI (hgI.const_mul t), integral_const_mul] at hcostmean

/-- A compact positive original quadratic coefficient turns the produced
kinetic integrability into a genuine full-displacement second moment. -/
theorem integrable_pair_displacement_sq_of_compact_quadratic
    (q : ℕ) (μ : Measure (PhysicalPairPalmMark (Fin q)))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (hμK : ∀ᵐ m ∂μ, m.1 ∈ K)
    (hkI : Integrable (fun m ↦ kin m.1.1 m.1.2 m.2) μ) :
    Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ ‖m.2‖ ^ 2) μ := by
  obtain ⟨c, hc, hlower⟩ := exists_uniform_matrixQuadratic_lower_bound hK hmatrix hpos
  apply (hkI.const_mul c⁻¹).mono' (by fun_prop)
  filter_upwards [hμK] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := hlower m.1 hm m.2
  rw [← hactual m.1 hm m.2] at h
  calc
    _ ≤ kin m.1.1 m.1.2 m.2 / c := (le_div_iff₀ hc).mpr (by nlinarith)
    _ = _ := by ring

end OTSelector.Reconstruction
