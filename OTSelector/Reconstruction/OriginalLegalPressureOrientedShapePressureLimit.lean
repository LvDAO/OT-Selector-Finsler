import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeFinitePressure
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapePartitionLimit
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeLimitTransfer
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHoleMass
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHoleRateNormalization
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonShape

/-! Native pressure is controlled by one actual inner oriented cube and its vanishing hole. -/

open Set Function MeasureTheory ProbabilityTheory Filter
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- A true two-piece spatial decomposition compares native and frame pressures.
The hole's iid matching, its actual Poisson counts, and the finite Hall repairs
are all constructed internally from the original population data. -/
theorem FiniteScalarBins.originalOrientedShape_pressure_limit_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (hIm : MeasurableSet I) (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β) (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hforward : ∀ᵐ p ∂π, gap ≤ p.2 - p.1)
    {diameter : ℝ} (hbounds : ConditionalClockSupportBounds α β gap diameter)
    {q : ℕ} (hq : 4 < q) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a d v, 0 ≤ kin a d v)
    (hkb : ∀ a d v, |kin a d v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c * v i) = c ^ 2 * kin a d v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a d, |g a d| ≤ G) (τ : ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 < s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1 / 2))
    (p0 p1 : ℝ)
    (hp0 : Tendsto (fun R ↦ legalMarkedScalePressure q id id α β kin g R τ)
      atTop (𝓝 p0))
    (hp1 : Tendsto (fun R ↦ legalMarkedScalePressure q id id α β
      (originalScreeningFrameKinetic b kin) g R τ) atTop (𝓝 p1)) :
    p0 ≤ s ^ q * p1 +
      (C * q * dyadicMatchingConstant q * ((D.count + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) *
        (1 - s ^ q) ^ (1 - 2 / (q : ℝ)) + |τ| * G * (1 - s ^ q) := by
  let H := (originalOrientedShapeUnitInner b s)ᶜ
  let h := (cubeMeasure (Fin q) 1).real H
  let K := ((D.count + 1 : ℕ) : ℝ)
  let A := C * (q : ℝ) * dyadicMatchingConstant q * K ^ (2 / (q : ℝ))
  let B := C * (q : ℝ) * ((1 + 2 * K) * Real.sqrt K + 2 * K)
  let L := |τ| * G
  let upper := fun r : ℝ≥0 ↦
    A * (r : ℝ) ^ (2 / (q : ℝ)) * ((r : ℝ) * h) ^ (1 - 2 / (q : ℝ)) +
      B * (r : ℝ) ^ (2 / (q : ℝ)) * Real.sqrt (2 * (r : ℝ) * h) + L * (r : ℝ) * h
  let repair := fun r : ℝ≥0 ↦ Real.sqrt (2 * (r : ℝ) * (2 * (D.count * D.count + 1))) *
    (2 * ((D.count : ℝ) + 1) * ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |τ| * G))
  have hH : MeasurableSet H := (measurableSet_originalOrientedShapeUnitInner b s).compl
  have hh : 0 ≤ h := measureReal_nonneg
  have hmass : h = 1 - s ^ q := originalOrientedShapeUnitHole_real_mass b hs.le hsub
  have horder : ∀ᵐ p ∂π, p.1 ≤ p.2 := hforward.mono fun _ hp ↦ by linarith
  have hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2 - p.1| := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae α.support_mem_ae,
      Measure.quasiMeasurePreserving_snd.ae β.support_mem_ae] with p hp ht
    simpa only [Real.dist_eq, abs_sub_comm] using hbounds.separated p.1 hp p.2 ht
  have hq0 : 0 < q := by omega
  have hθ : (0 : ℝ≥0) < Real.toNNReal (s ^ q) := Real.toNNReal_pos.mpr (pow_pos hs q)
  have hupper := tendsto_originalOrientedShape_hole_upper_div_nnreal hq A B L h hh
  have hcoe : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have herr : Tendsto (fun r : ℝ≥0 ↦ repair r / (r : ℝ)) atTop (𝓝 0) := by
    have he := (tendsto_originalOrientedShapePartition_repair_div_zero hq D.count 2 C G τ).comp
      hcoe
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      using he
  have hbound : ∀ᶠ r : ℝ≥0 in atTop,
      legalMarkedPressure q id id α β r kin g τ ≤
        legalMarkedPressure q id id α β (r * Real.toNNReal (s ^ q))
          (originalScreeningFrameKinetic b kin) g τ + upper r + repair r := by
    apply Filter.Eventually.of_forall
    intro r
    have hf := D.legalMarkedPressure_le_oriented_inner_and_hole hgap hIm π α β hπ hI
      hforward hsep hq0 b hs hsub r hC hG hk hkb hhom hg hgb τ
    have hh := (originalShapeHolePoisson_shape_mean_le hq α β π hπ D hIm hgap hbounds
      hI horder kin hk hkn hC hkb g hg hG hgb r H hH τ).2
    have hh' : (∫ ω, shapeLegalMarkedTilted q id id H r kin g τ ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β r) ≤ upper r := by
      simpa only [upper, A, B, L, K, mul_assoc] using hh
    exact hf.trans (add_le_add (add_le_add le_rfl hh') le_rfl)
  have hle := originalOrientedShape_scaled_normalized_limit_le
    (fun r ↦ legalMarkedPressure q id id α β r kin g τ)
    (fun r ↦ legalMarkedPressure q id id α β r (originalScreeningFrameKinetic b kin) g τ)
    upper repair hθ
    (tendsto_originalOrientedShape_pressure_div_nnreal q hq0 α β kin g τ p0 hp0)
    (tendsto_originalOrientedShape_pressure_div_nnreal q hq0 α β
      (originalScreeningFrameKinetic b kin) g τ p1 hp1) hupper herr hbound
  simpa only [Real.coe_toNNReal _ (pow_nonneg hs.le q), hmass, A, K, L, add_assoc]
    using hle

end OTSelector.Reconstruction
