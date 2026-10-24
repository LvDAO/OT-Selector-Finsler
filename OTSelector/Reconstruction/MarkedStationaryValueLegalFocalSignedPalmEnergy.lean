import OTSelector.Reconstruction.MarkedStationaryValueLegalDominatedPalmEnergy
import OTSelector.Reconstruction.MarkedStationaryValueLegalFocalEnergyCutoff
import OTSelector.Reconstruction.MarkedStationaryValueLegalSignedPalmEnergy
import OTSelector.Topology.CompactCutoffExhaustion

/-!
# The actual focal Palm signed energy survives degeneration at clock endpoints

Compact clock cutoffs stay inside the true open coefficient domain. Their
Tietze energy tests are dominated by the same original legal finite cost and
eventually agree with it at every original interior mark. Fatou's lemma then
recovers the full weighted Palm energy without requiring an endpoint lower
bound or a finite unweighted displacement second moment.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance markedStationaryValueLegalFocalSignedPalmEnergyInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalFocalSignedPalmEnergyPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Interior continuity suffices for the full original shifted Palm energy
bound. All cutoff extensions are charged to the same actual finite legal
optimizers and the same actual joint weak limit. -/
theorem lintegral_cubePalm_legalMarkedInputPairLaw_shifted_le_of_interior
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
    {domain : Set (ℝ × ℝ)} (hopen : IsOpen domain)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix domain) (hpos : ∀ w ∈ domain, (matrix w).PosSemidef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ domain)
    (hactual : ∀ a ∈ A, ∀ b ∈ B, a < b → ∀ v,
      kin a b v = matrixQuadratic (matrix (a, b)) v)
    (hgc : ContinuousOn (Function.uncurry g) domain)
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
    (∫⁻ m, ENNReal.ofReal (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G)
      ∂cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) ≤
      ENNReal.ofReal (p + |t| * G) := by
  let μ := cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))
  let W : Set (ℝ × ℝ) := {w | w.1 ∈ A ∧ w.2 ∈ B ∧ w.1 < w.2}
  have hprob := probability_cubePalm_of_legalMarkedInputSceneLaw_tendsto q α β kin hk g hg t
    L hL hlarge hweak hstat hfull
  have hμW : ∀ᵐ m ∂μ, m.1 ∈ W := ae_pair_clockCarrier_of_original_marginals q μ α β
    hprob.2.1 hprob.2.2 hA hB hα hβ hδ
    (ae_cubePalm_legalMarkedInputPairLaw_clockGap q hq α β kin hk g hg t L hL hweak hsep)
    (fun _ ha _ hb hab ↦ ⟨ha, hb, hab⟩)
  obtain ⟨χ, hχ, hχdom, hχevent⟩ := exists_compact_cutoffs_eventually_one_of_isOpen domain hopen
  choose F hFn hFeq hFle using fun n ↦ exists_continuous_legal_clockCutoff_shifted_minorant q
    matrix hmatrix hpos hkn (fun w (hw : w ∈ W) v ↦ hactual w.1 hw.1 w.2 hw.2.1 hw.2.2 v)
    hgc hgb t (χ n) (hχ n) (hχdom n)
  have hbound (n : ℕ) : (∫⁻ m, ENNReal.ofReal (F n m) ∂μ) ≤ ENNReal.ofReal (p + |t| * G) :=
    lintegral_cubePalm_legalMarkedInputPairLaw_continuous_dominated_shifted_le q hq α β hC hG hk
      hkn hkb hhom hg hgb t p hp hA hB hα hβ (fun a ha b hb hab ↦ (show (a, b) ∈ W from ⟨ha, hb, hab⟩))
      (F n) (hFn n) (hFle n) L hL hlarge hweak
  have hconv : ∀ᵐ m ∂μ, Tendsto (fun n ↦ ENNReal.ofReal (F n m)) atTop
      (𝓝 (ENNReal.ofReal (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G))) := by
    filter_upwards [hμW] with m hm
    apply tendsto_const_nhds.congr'
    filter_upwards [hχevent m.1 (hlegal m.1.1 hm.1 m.1.2 hm.2.1 hm.2.2)] with n hn
    rw [hFeq n m hm, hn, one_mul]
  calc
    _ = ∫⁻ m, liminf (fun n ↦ ENNReal.ofReal (F n m)) atTop ∂μ :=
      lintegral_congr_ae (hconv.mono (fun _ hm ↦ hm.liminf_eq.symm))
    _ ≤ liminf (fun n ↦ ∫⁻ m, ENNReal.ofReal (F n m) ∂μ) atTop :=
      lintegral_liminf_le (fun n ↦ (F n).continuous.measurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal (p + |t| * G) := by
      apply liminf_le_of_le (by isBoundedDefault)
      intro b hb
      obtain ⟨n, hn⟩ := hb.exists
      exact hn.trans (hbound n)

/-- The full actual focal probability Palm has integrable original weighted
kinetic and probe readouts and signed value at most the original pressure.
No unweighted displacement moment is claimed. -/
theorem integrable_signed_cubePalm_le_legalMarkedPressure_limit_of_interior
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
    {domain : Set (ℝ × ℝ)} (hopen : IsOpen domain)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix domain) (hpos : ∀ w ∈ domain, (matrix w).PosSemidef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ domain)
    (hactual : ∀ a ∈ A, ∀ b ∈ B, a < b → ∀ v,
      kin a b v = matrixQuadratic (matrix (a, b)) v)
    (hgc : ContinuousOn (Function.uncurry g) domain)
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
  let shift (m : PhysicalPairPalmMark (Fin q)) := kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G
  have hmeas : Measurable shift :=
    (hk.add (measurable_const.mul (hg.comp measurable_fst))).add measurable_const
  have hn (m : PhysicalPairPalmMark (Fin q)) : 0 ≤ shift m := by
    have hb : |t * g m.1.1 m.1.2| ≤ |t| * G := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgb m.1.1 m.1.2) (abs_nonneg t)
    dsimp [shift]
    linarith [(abs_le.mp hb).1, hkn m.1.1 m.1.2 m.2]
  have hbound := lintegral_cubePalm_legalMarkedInputPairLaw_shifted_le_of_interior q hq α β
    hC hG hk hkn hkb hhom hg hgb t p hp hA hB hα hβ hopen matrix hmatrix hpos
    hlegal hactual hgc hδ hsep L hL hlarge hweak hstat hfull
  have hshiftI : Integrable shift μ := ⟨hmeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (.of_forall hn)).mpr (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  have hlow : -(|t| * G) ≤ p := by
    apply ge_of_tendsto hp
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact legalMarkedScalePressure_lower_bound q measurable_id measurable_id α β hC hG hk hkn hkb hg hgb t hR
  have hmean : (∫ m, shift m ∂μ) ≤ p + |t| * G := by
    rw [← ofReal_integral_eq_lintegral_ofReal hshiftI (.of_forall hn)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ p + |t| * G)).mp hbound
  let cost (m : PhysicalPairPalmMark (Fin q)) := kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
  have heq : (fun m ↦ shift m - |t| * G) =ᵐ[μ] cost := .of_forall (fun m ↦ by
    dsimp [shift, cost]
    ring)
  have hcostI : Integrable cost μ := (hshiftI.sub (integrable_const _)).congr heq
  have hcostmean : (∫ m, cost m ∂μ) ≤ p := by
    calc
      _ = ∫ m, shift m - |t| * G ∂μ := (integral_congr_ae heq).symm
      _ = (∫ m, shift m ∂μ) - |t| * G := by rw [integral_sub hshiftI (integrable_const _)]; simp
      _ ≤ p := by linarith
  have hgI : Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ g m.1.1 m.1.2) μ :=
    Integrable.of_bound (hg.comp (measurable_fst.fst.prodMk measurable_fst.snd)).aestronglyMeasurable
      G (.of_forall (fun m ↦ by simpa only [Real.norm_eq_abs] using hgb m.1.1 m.1.2))
  have hkI : Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ kin m.1.1 m.1.2 m.2) μ :=
    (hcostI.sub (hgI.const_mul t)).congr (.of_forall (fun m ↦ by dsimp [cost]; ring))
  refine ⟨hkI, hgI, ?_⟩
  change (∫ m, kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 ∂μ) ≤ p at hcostmean
  rwa [integral_add hkI (hgI.const_mul t), integral_const_mul] at hcostmean

end OTSelector.Reconstruction
