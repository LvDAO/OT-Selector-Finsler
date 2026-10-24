import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalKinetic

/-!
# A genuine finite-second-moment reserve for the original focal cost

The constant identity coefficient first produces a full stationary matching
of the unchanged original Poisson inputs. Its finite displacement second
moment permits reweighting on exactly the same law by every measurable
quadratically bounded kinetic cost and every bounded measurable clock probe.
No positive lower bound for the original focal coefficient is used.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff CompactlySupported Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-- The finite displacement second moment controls every nonnegative
quadratic-sum upper bound, on the unchanged actual Palm measure. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_of_quadratic_bound
    {q : ℕ} {α β : Measure ℝ} {kin₀ : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g₀ : ℝ → ℝ → ℝ} (Q : LegalWeightedStationaryPoissonMatching q α β kin₀ g₀)
    (hsecond : Integrable (fun m ↦ ‖m.2‖ ^ 2) (legalMarkedJointPalm q Q.law))
    {C : ℝ} (hC : 0 ≤ C) {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ ↦ kin z.1 z.2)))
    (hbound : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2) :
    Integrable (fun m ↦ kin m.1.1 m.1.2 m.2) (legalMarkedJointPalm q Q.law) := by
  apply (hsecond.const_mul (C * q)).mono' hk.aestronglyMeasurable
  filter_upwards [] with m
  change |kin m.1.1 m.1.2 m.2| ≤ C * (q : ℝ) * ‖m.2‖ ^ 2
  have hsum : ∑ i, m.2 i ^ 2 ≤ (q : ℝ) * ‖m.2‖ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin q, ‖m.2‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |m.2 i| ≤ ‖m.2‖ := norm_le_pi_norm m.2 i
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hi
      _ = _ := by simp
  exact (hbound _ _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hsum hC])

/-- A bounded measurable clock probe is integrable on the actual unchanged
probability Palm. No continuity at focal support endpoints is required. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_bounded_clock_probe
    {q : ℕ} {α β : Measure ℝ} {kin₀ : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g₀ : ℝ → ℝ → ℝ} (Q : LegalWeightedStationaryPoissonMatching q α β kin₀ g₀)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hbound : ∀ a b, |g a b| ≤ G) :
    Integrable (fun m ↦ g m.1.1 m.1.2) (legalMarkedJointPalm q Q.law) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  apply (integrable_const G).mono' (hg.comp measurable_fst).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun m ↦ hbound m.1.1 m.1.2)

/-- Reweight the same genuine matching, retaining its original input law,
full matching, clock marginals and true source-anchored Palm exactly. -/
def LegalWeightedStationaryPoissonMatching.reweightOfFiniteSecondMoment
    {q : ℕ} {α β : Measure ℝ} {kin₀ : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g₀ : ℝ → ℝ → ℝ} (Q : LegalWeightedStationaryPoissonMatching q α β kin₀ g₀)
    (hsecond : Integrable (fun m ↦ ‖m.2‖ ^ 2) (legalMarkedJointPalm q Q.law))
    {C : ℝ} (hC : 0 ≤ C) {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ ↦ kin z.1 z.2)))
    (hbound : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    LegalWeightedStationaryPoissonMatching q α β kin g where
  law := Q.law
  stationary := Q.stationary
  full_matching := Q.full_matching
  forward := Q.forward
  input_laplace := Q.input_laplace
  palm_probability := Q.palm_probability
  source_clock := Q.source_clock
  target_clock := Q.target_clock
  kinetic_integrable := Q.integrable_of_quadratic_bound hsecond hC hk hbound
  probe_integrable := Q.integrable_bounded_clock_probe hg hgb

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original Finsler clock laws admit a genuine full stationary Poisson
matching with finite displacement second moment and finite original focal
energy, for any bounded measurable original probe. The auxiliary identity
cost constructs only the reserve law; the returned cost is the original one. -/
theorem exists_original_focal_finiteSecondMoment_stationaryMatching
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g,
      Integrable (fun m ↦ ‖m.2‖ ^ 2)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let I : Set ℝ := μ.support ∪ ν.support
  have hI : IsCompact I := hbounds.source_compact.union hbounds.target_compact
  obtain ⟨bins⟩ := exists_finiteScalarBins hI hgap
  have hsrc : ∀ᵐ p ∂π, p.1 ∈ μ.support :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact μ.support_mem_ae)
  have htgt : ∀ᵐ p ∂π, p.2 ∈ ν.support :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact ν.support_mem_ae)
  have hcarry : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I :=
    (hsrc.and htgt).mono (fun _ h ↦ ⟨Or.inl h.1, Or.inr h.2⟩)
  have hsep : ∀ᵐ p ∂μ.prod ν, gap ≤ |p.2 - p.1| := by
    filter_upwards [ae_fst_of_ae μ.support_mem_ae, ae_snd_of_ae ν.support_mem_ae] with p hp hq
    simpa only [Real.dist_eq, abs_sub_comm] using hbounds.separated p.1 hp p.2 hq
  let kin : ℝ → ℝ → (Fin q → ℝ) → ℝ := fun _ _ v ↦
    matrixQuadratic (1 : Matrix (Fin q) (Fin q) ℝ) v
  have hk : Measurable (Function.uncurry (fun z : ℝ × ℝ ↦ kin z.1 z.2)) := by
    exact continuous_matrixQuadratic.measurable.comp (measurable_const.prodMk measurable_snd)
  have hkeq (a b : ℝ) (v : Fin q → ℝ) : kin a b v = (1 / 2 : ℝ) * ∑ i, v i ^ 2 := by
    simp [kin, matrixQuadratic, dotProduct, pow_two]
  have hkn : ∀ a b v, 0 ≤ kin a b v := by
    intro a b v
    rw [hkeq a b v]
    positivity
  have hkb : ∀ a b v, |kin a b v| ≤ 1 * ∑ i, v i ^ 2 := by
    intro a b v
    rw [abs_of_nonneg (hkn a b v), hkeq a b v]
    have hs : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    linarith
  obtain ⟨p, hp, hc, hl, hscene⟩ :=
    bins.exists_legalWeightedStationaryPoissonMatching_energy_le hgap hI.measurableSet
      π μ ν hπ hcarry (hbounds.ae_clock_gap_of_coupling hπ horder) hsep q hq
      (C := 1) (G := 0) (by norm_num) (by norm_num) hk hkn hkb
      (fun a b c _ v ↦ matrixQuadratic_smul 1 c v)
      (g := fun _ _ ↦ 0) measurable_const (by intro a b; simp)
      hbounds.source_compact hbounds.target_compact μ.measure_compl_support ν.measure_compl_support
      (K := μ.support ×ˢ ν.support) (hbounds.source_compact.prod hbounds.target_compact)
      (fun _ ↦ 1) continuousOn_const (fun _ _ ↦ Matrix.PosDef.one)
      (fun _ ha _ hb _ ↦ ⟨ha, hb⟩) (fun _ _ _ ↦ rfl) continuousOn_const
  obtain ⟨Q, hsecond, _⟩ := hscene 0
  obtain ⟨C, hC, hbound⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  exact ⟨Q.reweightOfFiniteSecondMoment hsecond hC
    (D.measurable_originalFocalKinetic hF hw gap) hbound hg hgb, hsecond⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
