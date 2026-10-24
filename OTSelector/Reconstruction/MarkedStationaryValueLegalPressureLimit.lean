import OTSelector.Reconstruction.MarkedStationaryValueLegalBlockSubadditivity
import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureBound
import OTSelector.Reconstruction.MarkedStationaryValueLegalIntensityContinuity
import OTSelector.Analysis.Convex.SubadditiveLimit

/-!
# Actual forward legal Poisson pressure limit

The original strict-clock maximum-cardinality matching value has a real-scale
thermodynamic limit for q > 4. Finite scalar population types produce the actual
grid deficits and legal alternating-path repairs; exact prefix laws produce the
leaf pressures. No complete-bipartite pressure limit is used for this result.
-/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The actual original forward legal maximum-cardinality Poisson pressure
converges along every real spatial scale, to a concave G-Lipschitz tilt function.
All finite-count, leaf-law, repair, boundedness and continuity inputs are produced
from the original compact scalar-bin population and kernel data. -/
theorem exists_legalMarkedScalePressure_limit_of_scalarBins
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ) (hIm : MeasurableSet I)
    (source : A → ℝ) (target : B → ℝ) (hs : Measurable source) (ht : Measurable target)
    (π : Measure (A × B)) [IsFiniteMeasure π]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (hsep : ∀ᵐ p ∂α.prod β, δ ≤ |target p.2 - source p.1|)
    (q : ℕ) (hq : 4 < q) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure q source target α β kin probe R t)
        atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p := by
  let K := legalGridRepairConstant q D.count (legalClockTypeCount D.count)
  have hK : 0 ≤ K := (legal_grid_repair_sum_le q 0 D.count (legalClockTypeCount D.count)
    hq 1 (by norm_num) (by norm_num) (r := 0) (C := 0) (G := 0) (t := 0)
    le_rfl le_rfl le_rfl).1
  have hsource : ∀ᵐ a ∂α, source a ∈ I := by
    rw [← hπ.1]
    exact (ae_map_iff measurable_fst.aemeasurable (hs hIm)).mpr (hI.mono (fun _ h ↦ h.1))
  have hblock (t : ℝ) (m : ℕ) (hm : 0 < m) (L : ℝ) (hL : 0 < L) :
      legalMarkedScalePressure q source target α β kin probe ((m : ℝ) * L) t ≤
        legalMarkedScalePressure q source target α β kin probe L t + gridRepairError q K C G t L := by
    apply legalMarkedScalePressure_block_le_of_intensity_bound q m (by omega) hm
      source target α β kin probe C G t K _ hL
    intro r
    exact legalMarkedPressure_le_blockScale_add_repair D hδ hIm source target hs ht
      π α β hπ hI hgap hsep q hq m hm r hC hG hk hkb hhom hp hpb t
  refine OTSelector.exists_tendsto_of_block_subadditive_of_tiltError hG
    (exists_legalMarkedScalePressure_bound_of_block q hq hs ht α β hC hG hK hk hkn hkb hp hpb hblock)
    (fun R ↦ concaveOn_legalMarkedScalePressure q hs ht α β hC hG hk
      (fun a b _ ↦ hkb a b) hp (fun a b _ ↦ hpb a b) R)
    (fun R t u ↦ legalMarkedScalePressure_lipschitz q hs ht α β hC hG hk
      (fun a b _ ↦ hkb a b) hp (fun a b _ ↦ hpb a b) R t u)
    (fun t L hL ↦ (D.continuousOn_legalMarkedScalePressure hδ q hs ht α β hsource hsep
      hC hG hk hkb hp hpb t).continuousAt (isOpen_Ioi.mem_nhds hL))
    (fun t L ↦ gridRepairError q K C G t L)
    (fun t L hL ↦ (continuousAt_gridRepairError q K C G t hL).tendsto)
    (fun t ↦ tendsto_gridRepairError_atTop hq K C G t) ?_
  intro t L hL ε hε
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have h := hblock t m hm L hL
  linarith

/-- A real-scale limit of the actual legal pressure transfers to intensity
normalization with the same limiting value. -/
theorem tendsto_legalMarkedPressure_div (q : ℕ) (hq : 0 < q)
    (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R ↦ legalMarkedScalePressure q source target α β kin probe R t)
      atTop (𝓝 (p t))) :
    ∀ t, Tendsto (fun r : ℝ ↦
      legalMarkedPressure q source target α β (Real.toNNReal r) kin probe t / r)
      atTop (𝓝 (p t)) := by
  intro t
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : Tendsto (fun r : ℝ ↦ r ^ (1 / (q : ℝ))) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hcomp := (hp t).comp hpow
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  change legalMarkedScalePressure q source target α β kin probe (r ^ (1 / (q : ℝ))) t =
    legalMarkedPressure q source target α β (Real.toNNReal r) kin probe t / r
  simp only [legalMarkedScalePressure, Real.rpow_pos_of_pos hr _, ↓reduceIte]
  have hpowq : (r ^ (1 / (q : ℝ))) ^ q = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    have hq1 : (1 / (q : ℝ)) * (q : ℝ) = 1 := by field_simp
    rw [hq1, Real.rpow_one]
  rw [hpowq]

end OTSelector.Reconstruction
