import OTSelector.Reconstruction.MarkedStationaryValueLegalGridPressure
import OTSelector.Reconstruction.MarkedStationaryValueLegalGridArithmetic
import OTSelector.Probability.GridRepairScaling

/-! Actual original legal pressure block subadditivity with explicit vanishing
repair error. The population chart is chosen internally to be the singleton. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The exact finite scalar-bin type count for the singleton population chart. -/
def legalClockTypeCount (bins : ℕ) : ℕ := Fintype.card (Option (Unit × Fin bins × Fin bins))

theorem legalClockTypeCount_eq (bins : ℕ) : legalClockTypeCount bins = 1 + bins * bins := by
  simp [legalClockTypeCount, Fintype.card_option, Fintype.card_prod, Nat.add_comm]

/-- Actual legal pressure subadditivity at every intensity and natural block
count, produced solely from original clock population and compact-bin data. -/
theorem legalMarkedPressure_le_blockScale_add_repair
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ) (hIm : MeasurableSet I)
    (source : A → ℝ) (target : B → ℝ) (hs : Measurable source) (ht : Measurable target)
    (π : Measure (A × B)) [IsFiniteMeasure π]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (hsep : ∀ᵐ p ∂α.prod β, δ ≤ |target p.2 - source p.1|)
    (q : ℕ) (hq : 4 < q) (m : ℕ) (hm : 0 < m) (r : ℝ≥0)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    legalMarkedPressure q source target α β r kin probe t ≤
      ((m ^ q : ℕ) : ℝ) *
        legalMarkedPressure q source target α β (r / (m ^ q : ℝ≥0)) kin probe t +
      legalGridRepairConstant q D.count (legalClockTypeCount D.count) * (C + |t| * G) * (r : ℝ) *
        (Real.rpow ((r : ℝ) / (m : ℝ) ^ q) (2 / (q : ℝ) - 1 / 2) +
          Real.rpow ((r : ℝ) / (m : ℝ) ^ q) (-(1 / 2))) := by
  let : MeasurableSpace (Option (Unit × Fin D.count × Fin D.count)) := ⊤
  let : DiscreteMeasurableSpace (Option (Unit × Fin D.count × Fin D.count)) := ⟨fun _ ↦ trivial⟩
  obtain ⟨depth, hdepth, hdepth2⟩ := exists_gridLevel m hm
  have hpressure := scalarBinPopulationTypes_legalPressure_le_grid D hδ hIm
    (fun _ : A × B ↦ ()) source target π α β hπ measurable_const hs ht hI hgap hsep
    q m depth (by omega) hm hdepth hdepth2 r hC hG hk hkb hhom hp hpb t
  have herror := (legal_grid_repair_sum_le q depth D.count (legalClockTypeCount D.count)
    hq m hm hdepth2 (t := t) r.coe_nonneg hC hG).2
  exact hpressure.trans (add_le_add le_rfl herror)

/-- Algebraic scale normalization of an actual legal intensity comparison. -/
theorem legalMarkedScalePressure_block_le_of_intensity_bound
    (q m : ℕ) (hq : 0 < q) (hm : 0 < m)
    (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (C G t K : ℝ)
    (hpressure : ∀ r : ℝ≥0, legalMarkedPressure q source target α β r kin probe t ≤
      ((m ^ q : ℕ) : ℝ) * legalMarkedPressure q source target α β (r / (m ^ q : ℝ≥0)) kin probe t +
      K * (C + |t| * G) * (r : ℝ) *
        (Real.rpow ((r : ℝ) / (m : ℝ) ^ q) (2 / (q : ℝ) - 1 / 2) +
          Real.rpow ((r : ℝ) / (m : ℝ) ^ q) (-(1 / 2)))) {L : ℝ} (hL : 0 < L) :
    legalMarkedScalePressure q source target α β kin probe ((m : ℝ) * L) t ≤
      legalMarkedScalePressure q source target α β kin probe L t + gridRepairError q K C G t L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmL : 0 < (m : ℝ) * L := mul_pos hmR hL
  have hLq : 0 < L ^ q := pow_pos hL q
  simp only [legalMarkedScalePressure, hmL, hL, ↓reduceIte]
  have hred : ((Real.toNNReal (((m : ℝ) * L) ^ q) / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ) = L ^ q := by
    rw [NNReal.coe_div, Real.coe_toNNReal _ (by positivity)]
    push_cast
    exact mul_pow_div_pow q m hm L
  have hred_eq : Real.toNNReal (((m : ℝ) * L) ^ q) / (m ^ q : ℝ≥0) = Real.toNNReal (L ^ q) := by
    apply NNReal.coe_injective
    rw [hred, Real.coe_toNNReal _ hLq.le]
  have hbase := hpressure (Real.toNNReal (((m : ℝ) * L) ^ q))
  rw [hred_eq, Real.coe_toNNReal _ (pow_nonneg hmL.le q),
    rpow_div_mul_pow_kinetic q hq hL m hm, rpow_div_mul_pow_probe q hq hL m hm] at hbase
  apply (div_le_iff₀ (pow_pos hmL q)).mpr
  have hcoef : ((m ^ q : ℕ) : ℝ) * legalMarkedPressure q source target α β
      (Real.toNNReal (L ^ q)) kin probe t =
      (legalMarkedPressure q source target α β (Real.toNNReal (L ^ q)) kin probe t / L ^ q) *
        ((m : ℝ) * L) ^ q := by
    rw [mul_pow]
    push_cast
    field_simp
  rw [gridRepairError, add_mul, ← hcoef]
  nlinarith [hbase]

end OTSelector.Reconstruction
