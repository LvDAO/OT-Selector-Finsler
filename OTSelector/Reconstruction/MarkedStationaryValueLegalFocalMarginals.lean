import OTSelector.Reconstruction.MarkedStationaryValueLegalFocalEscape
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputSourceMarginal
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputTargetMarginal

/-!
# Full original input recovery with genuine focal clock collars

Both complete endpoint marginals of the same actual joint weak limit are
recovered using interior collar escape control. No coefficient positivity at
focal support endpoints or proper endpoint projection is assumed.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Metric
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalFocalMarginalsInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalFocalMarginalsPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Original finite legal deficits and actual interior coefficient collars recover
the complete source input of the same weak limit. -/
theorem ae_legalMarkedInput_source_marginal_eq_of_sourceDefect_of_interior
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hdef : Tendsto (fun R : ℝ ↦
      (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (R ^ q))) / R ^ q) atTop (𝓝 0))
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
    {J A₀ B₀ : Set ℝ} (hJ : MeasurableSet J)
    (hA₀ : MeasurableSet A₀) (hB₀ : MeasurableSet B₀)
    (hαJ : α Jᶜ = 0) (hβJ : β Jᶜ = 0)
    (hαA : α A₀ᶜ = 0) (hβB : β B₀ᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ A₀, ∀ b ∈ B₀, δ ≤ |b - a|)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix {p | p.1 ∈ J ∧ p.2 ∈ J ∧ p.1 < p.2})
    (hpos : ∀ p, p.1 ∈ J → p.2 ∈ J → p.1 < p.2 → (matrix p).PosDef)
    (hactual : ∀ a ∈ J ∩ A₀, ∀ b ∈ J ∩ B₀, a < b → ∀ v,
      kin a b v = matrixQuadratic (matrix (a, b)) v)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 := by
  apply ae_legalMarkedInput_marginal_eq_of_cutoff_budgets q Q _ hweak
    (fun s : LegalMarkedOptimalInputScene q ↦ s.1.1) continuous_fst.fst 0
    (fun f k ↦ legalMarkedRootedSourceTestError q (L k) α β kin g t f)
  · intro f
    obtain ⟨b, hb, hbound⟩ := (f.hasCompactSupport.image continuous_fst).isBounded.exists_pos_norm_lt
    have hzero : ∀ x : LegalMarkedPhysicalPoint q, x.1 ∉ ball (0 : Fin q → ℝ) b → f x = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (by
        simpa only [mem_ball, dist_zero_right] using hbound _ ⟨x, hs, rfl⟩))
    have hfb : ∀ x, |f x| ≤ ‖f.toBoundedContinuousFunction‖ :=
      fun x ↦ f.toBoundedContinuousFunction.norm_coe_le_norm x
    exact ((tendsto_legalMarkedRooted_spatialTestErrors_of_sourceDefect q α β hk hg t
      (h := fun x ↦ f x) f.continuous.measurable hfb
      (ball (0 : Fin q → ℝ) b) measurableSet_ball measure_ball_lt_top.ne hzero hdef).1).comp hlarge
  · intro f ε hε
    obtain ⟨b, hb, hbound⟩ := (f.hasCompactSupport.image continuous_fst).isBounded.exists_pos_norm_lt
    have hcover : ∀ x ∈ tsupport f, x.1 ∈ ball (0 : Fin q → ℝ) b := by
      intro x hx
      simpa only [mem_ball, dist_zero_right] using hbound _ ⟨x, hx, rfl⟩
    have hbounded : ∀ x ∈ ball (0 : Fin q → ℝ) b, ‖x‖ ≤ b := by
      intro x hx
      exact (by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < b).le
    obtain ⟨L₀, hescape⟩ := exists_uniform_legalMarkedOptimalRootedSceneLaw_compact_bounds_of_interior
      q hq α β hC hG hk hkn hkb hhom hg hgb t p hp hJ hA₀ hB₀ hαJ hβJ hαA hβB hδ hsep
      matrix hmatrix hpos hactual measurableSet_ball measure_ball_lt_top.ne hbounded
    obtain ⟨S, T, hS, hT, htail⟩ := hescape ε hε
    refine ⟨T, hT, fun χ hχ hχT ↦ ?_⟩
    filter_upwards [hlarge.eventually (eventually_ge_atTop L₀)] with k hklarge
    have hb := (lintegral_abs_legalMarkedInputSourceCutoffDefect_le q hq α β kin hk g hg t
      (hL k) f χ hχ (hT).isClosed hχT isOpen_ball hcover).trans
      (add_le_add le_rfl (mul_le_mul_right ((htail (L k) (hL k) hklarge).1) _))
    simpa only [legalMarkedInputSourceCutoffDefect] using hb


/-- Original finite legal deficits and actual interior coefficient collars recover
the complete target input of the same weak limit. -/
theorem ae_legalMarkedInput_target_marginal_eq_of_sourceDefect_of_interior
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hdef : Tendsto (fun R : ℝ ↦
      (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (R ^ q))) / R ^ q) atTop (𝓝 0))
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
    {J A₀ B₀ : Set ℝ} (hJ : MeasurableSet J)
    (hA₀ : MeasurableSet A₀) (hB₀ : MeasurableSet B₀)
    (hαJ : α Jᶜ = 0) (hβJ : β Jᶜ = 0)
    (hαA : α A₀ᶜ = 0) (hβB : β B₀ᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ A₀, ∀ b ∈ B₀, δ ≤ |b - a|)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix {p | p.1 ∈ J ∧ p.2 ∈ J ∧ p.1 < p.2})
    (hpos : ∀ p, p.1 ∈ J → p.2 ∈ J → p.1 < p.2 → (matrix p).PosDef)
    (hactual : ∀ a ∈ J ∩ A₀, ∀ b ∈ J ∩ B₀, a < b → ∀ v,
      kin a b v = matrixQuadratic (matrix (a, b)) v)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1 := by
  have h := ae_legalMarkedInput_marginal_eq_of_cutoff_budgets q Q _ hweak
    (fun s : LegalMarkedOptimalInputScene q ↦ LocalFiniteMeasure.swapEndpoints s.1.1)
    (LocalFiniteMeasure.continuous_swapEndpoints.comp continuous_fst.fst) 1
    (fun f k ↦ legalMarkedRootedTargetTestError q (L k) α β kin g t f)
    (by
      intro f
      obtain ⟨b, hb, hbound⟩ := (f.hasCompactSupport.image continuous_fst).isBounded.exists_pos_norm_lt
      have hzero : ∀ x : LegalMarkedPhysicalPoint q, x.1 ∉ ball (0 : Fin q → ℝ) b → f x = 0 := by
        intro x hx
        exact image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (by
          simpa only [mem_ball, dist_zero_right] using hbound _ ⟨x, hs, rfl⟩))
      have hfb : ∀ x, |f x| ≤ ‖f.toBoundedContinuousFunction‖ :=
        fun x ↦ f.toBoundedContinuousFunction.norm_coe_le_norm x
      exact ((tendsto_legalMarkedRooted_spatialTestErrors_of_sourceDefect q α β hk hg t
        (h := fun x ↦ f x) f.continuous.measurable hfb
        (ball (0 : Fin q → ℝ) b) measurableSet_ball measure_ball_lt_top.ne hzero hdef).2).comp hlarge
    ) (by
      intro f ε hε
      obtain ⟨b, hb, hbound⟩ := (f.hasCompactSupport.image continuous_fst).isBounded.exists_pos_norm_lt
      have hcover : ∀ x ∈ tsupport f, x.1 ∈ ball (0 : Fin q → ℝ) b := by
        intro x hx
        simpa only [mem_ball, dist_zero_right] using hbound _ ⟨x, hx, rfl⟩
      have hbounded : ∀ x ∈ ball (0 : Fin q → ℝ) b, ‖x‖ ≤ b := by
        intro x hx
        exact (by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < b).le
      obtain ⟨L₀, hescape⟩ := exists_uniform_legalMarkedOptimalRootedSceneLaw_compact_bounds_of_interior
        q hq α β hC hG hk hkn hkb hhom hg hgb t p hp hJ hA₀ hB₀ hαJ hβJ hαA hβB hδ hsep
        matrix hmatrix hpos hactual measurableSet_ball measure_ball_lt_top.ne hbounded
      obtain ⟨S, T, hS, hT, htail⟩ := hescape ε hε
      refine ⟨S, hS, fun χ hχ hχT ↦ ?_⟩
      filter_upwards [hlarge.eventually (eventually_ge_atTop L₀)] with k hklarge
      have hb := (lintegral_abs_legalMarkedInputTargetCutoffDefect_le q hq α β kin hk g hg t
        (hL k) f χ hχ (hS).isClosed hχT isOpen_ball hcover).trans
        (add_le_add le_rfl (mul_le_mul_right ((htail (L k) (hL k) hklarge).2) _))
      simpa only [legalMarkedInputTargetCutoffDefect, LocalFiniteMeasure.testIntegral_swapEndpoints_product] using hb
    )
  simpa only [LocalFiniteMeasure.swapEndpoints_fst] using h


end OTSelector.Reconstruction
