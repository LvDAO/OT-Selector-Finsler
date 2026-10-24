import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointExpectation
import OTSelector.Reconstruction.LegalInputMarginalClosure

/-!
# The actual legal optimal weak scene uses every original source input

The source deficit comes from the original legal maximum-cardinality count,
and compact target escape comes from the actual legal pressure and the original
positive quadratic coefficient. These analytic producers remove both budgets
before the countable compact-test code identifies the full nonproper marginal.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Metric
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInputSourceMarginalInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputSourceMarginalPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The original legal source-defect density and actual compact coercivity
force the complete matching source marginal to equal its own original input.
No projected marginal finiteness, escaped-mass or cutoff-error input is supplied. -/
theorem ae_legalMarkedInput_source_marginal_eq_of_sourceDefect
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
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
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
    obtain ⟨L₀, hescape⟩ := exists_uniform_legalMarkedOptimalRootedSceneLaw_target_compact_bound
      q hq α β hC hG hk hkn hkb hhom hg hgb t p hp hA hB hα hβ hK matrix hmatrix hpos hlegal
      hactual measurableSet_ball measure_ball_lt_top.ne hbounded
    obtain ⟨T, hT, htail⟩ := hescape ε hε
    refine ⟨T, hT, fun χ hχ hχT ↦ ?_⟩
    filter_upwards [hlarge.eventually (eventually_ge_atTop L₀)] with k hklarge
    have hb := (lintegral_abs_legalMarkedInputSourceCutoffDefect_le q hq α β kin hk g hg t
      (hL k) f χ hχ (hT).isClosed hχT isOpen_ball hcover).trans
      (add_le_add le_rfl (mul_le_mul_right (htail (L k) (hL k) hklarge) _))
    simpa only [legalMarkedInputSourceCutoffDefect] using hb

/-- The original scalar-bin coupling supplies the missing-source density itself;
the same actual legal optimal joint weak limit therefore has full source input. -/
theorem FiniteScalarBins.ae_legalMarkedInput_source_marginal_eq
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ z ∂π, z.1 ∈ I ∧ z.2 ∈ I) (hgap : ∀ᵐ z ∂π, δ ≤ z.2 - z.1)
    (q : ℕ) (hq : 0 < q)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ ↦ kin z.1 z.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t p : ℝ)
    (hp : Tendsto (fun R ↦ legalMarkedScalePressure q id id α β kin g R t) atTop (𝓝 p))
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 :=
  ae_legalMarkedInput_source_marginal_eq_of_sourceDefect q hq α β
    (scalarBins_legalMarkedSourceDefect_div_tendsto_zero D hδ π α β hπ hI hgap q hq)
    hC hG hk hkn hkb hhom hg hgb t p hp hA hB hα hβ hK matrix hmatrix hpos hlegal hactual
    L hL hlarge hweak

end OTSelector.Reconstruction
