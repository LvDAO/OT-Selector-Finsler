import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import OTSelector.MeasureTheory.CompactProductMarginalTests
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests

/-!
## Lemma skeleton

* **Conditions:** Joint weak convergence, continuous plan/input projections and two vanishing error families.
* **Objects:** Full source or target input marginal equality in the weak scene.
* **Proof detail:** Pass test errors by semicontinuity, choose a cutoff subsequence, derive projected local finiteness and use countable separating probes.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47

**Relationship to the sources:** The two-error bookkeeping and derived projection finiteness are local mathematical combinations; generic names do not assert a textbook theorem with this full signature.
-/

/-!
# Common weak-scene input closure without a canonical optimizer

The weak laws and continuous plan/input projections are supplied unchanged.
Original finite readout errors and partner-cutoff errors are kept separate.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

section Weak
variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- Portmanteau transfers a continuous readout's eventual varying finite bound
through its actual weak law. -/
theorem lintegral_abs_le_of_weak_eventual_tendsto_bound
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q)) (H : S → ℝ) (hH : Continuous H)
    (B : ℕ → ℝ≥0∞) {C : ℝ≥0∞} (hB : Tendsto B atTop (𝓝 C))
    (hb : ∀ᶠ n in atTop, (∫⁻ s, ENNReal.ofReal |H s| ∂(P n : Measure S)) ≤ B n) :
    (∫⁻ s, ENNReal.ofReal |H s| ∂(Q : Measure S)) ≤ C := by
  apply (lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hH.abs (fun _ ↦ abs_nonneg _) (fun U hU ↦
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU)).trans
  exact (liminf_le_liminf hb).trans_eq hB.liminf_eq

omit [HasOuterApproxClosed S] in
/-- Vanishing nonnegative expectations force the pointwise liminf to vanish
on one actual-law AE event, without presuming a finite readout limit. -/
theorem ae_liminf_abs_eq_zero_of_lintegral_bounds
    (Q : ProbabilityMeasure S) (H : ℕ → S → ℝ) (hH : ∀ R, Continuous (H R))
    (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ R, (∫⁻ s, ENNReal.ofReal |H R s| ∂(Q : Measure S)) ≤ error R) :
    ∀ᵐ s ∂(Q : Measure S), atTop.liminf (fun R ↦ ENNReal.ofReal |H R s|) = 0 := by
  have hmeas (R : ℕ) : Measurable (fun s ↦ ENNReal.ofReal |H R s|) :=
    (hH R).abs.measurable.ennreal_ofReal
  have hlim : Tendsto (fun R ↦ ∫⁻ s, ENNReal.ofReal |H R s| ∂(Q : Measure S))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herror
      (fun _ ↦ zero_le) hbound
  have hz : (∫⁻ s, atTop.liminf (fun R ↦ ENNReal.ofReal |H R s|) ∂(Q : Measure S)) = 0 :=
    le_antisymm ((lintegral_liminf_le hmeas).trans_eq hlim.liminf_eq) zero_le
  exact (lintegral_eq_zero_iff' (Measurable.liminf hmeas).aemeasurable).mp hz

end Weak

section Marginal
variable {X Y S : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
  [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
  [SecondCountableTopology Y]
  [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S] [HasOuterApproxClosed S]

omit [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y] in
/-- At every actual finite scene the compact-product discrepancy is exactly
paid by the untruncated original input error and the actual partner escape.
This supplies the finite inequality needed by the weak closure below. -/
theorem ofReal_abs_input_sub_product_le_full_error_tail
    (π : Measure (X × Y)) [IsFiniteMeasure π] (ν : LocalFiniteMeasure X)
    (f : C_c(X, ℝ)) (g : C_c(Y, ℝ)) (hg : ∀ y, g y ∈ Icc 0 1)
    (K : Set Y) (hgK : EqOn g 1 K) :
    ENNReal.ofReal |LocalFiniteMeasure.testIntegral ν f -
      ∫ e, cavityProductTest f g e ∂π| ≤
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral ν f - ∫ e, f e.1 ∂π| +
        ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * π (tsupport f ×ˢ Kᶜ) := by
  have hf : Integrable (fun e : X × Y ↦ f e.1) π :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖
      (Eventually.of_forall fun e ↦ f.toBoundedContinuousFunction.norm_coe_le_norm e.1)
  have htail := abs_integral_source_sub_product_le_tail π f g hf hg K hgK (measure_lt_top _ _)
  have htail' : ENNReal.ofReal |(∫ e, f e.1 ∂π) - ∫ e, cavityProductTest f g e ∂π| ≤
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * π (tsupport f ×ˢ Kᶜ) := by
    have hh := ENNReal.ofReal_le_ofReal htail
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_measureReal (measure_ne_top π _)] at hh
    exact hh
  have htri := ENNReal.ofReal_le_ofReal (abs_sub_le (LocalFiniteMeasure.testIntegral ν f)
    (∫ e, f e.1 ∂π) (∫ e, cavityProductTest f g e ∂π))
  exact (htri.trans_eq (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _))).trans
    (add_le_add le_rfl htail')

omit [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X] [SigmaCompactSpace Y] in
/-- Vanishing cutoff discrepancy already prevents infinite source-window mass;
no local finiteness of the nonproper endpoint projection is presumed. -/
theorem lintegral_source_test_le_input_of_liminf_cutoff_defect_zero
    (π : LocalFiniteMeasure (X × Y)) (ν : LocalFiniteMeasure X)
    (f : C_c(X, ℝ)) (hf : ∀ x, 0 ≤ f x) (K : CompactExhaustion Y)
    (index : ℕ → ℕ) (hindex : Tendsto index atTop atTop)
    (hzero : atTop.liminf (fun R ↦ ENNReal.ofReal
      |LocalFiniteMeasure.testIntegral ν f - LocalFiniteMeasure.testIntegral π
        (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R)))|) = 0) :
    (∫⁻ e, ENNReal.ofReal (f e.1) ∂(π : Measure (X × Y))) ≤
      ENNReal.ofReal (LocalFiniteMeasure.testIntegral ν f) := by
  let A := fun R ↦ ENNReal.ofReal |LocalFiniteMeasure.testIntegral ν f -
    LocalFiniteMeasure.testIntegral π (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R)))|
  have hpt (e : X × Y) : Tendsto (fun R ↦ ENNReal.ofReal
      (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R)) e))
      atTop (𝓝 (ENNReal.ofReal (f e.1))) := by
    obtain ⟨R₀,hR₀⟩ := K.exists_mem e.2
    apply tendsto_const_nhds.congr'
    filter_upwards [hindex.eventually (eventually_ge_atTop R₀)] with R hR
    change ENNReal.ofReal (f e.1) = ENNReal.ofReal
      (f e.1 * LocalFiniteMeasure.exhaustionCutoff K (index R) e.2)
    have hx : LocalFiniteMeasure.exhaustionCutoff K (index R) e.2 = (1 : ℝ) :=
      LocalFiniteMeasure.exhaustionCutoff_eq_one K (index R) (K.subset hR hR₀)
    rw [hx, mul_one]
  have hnonneg (R : ℕ) (e : X × Y) : 0 ≤
      cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R)) e :=
    mul_nonneg (hf e.1) (LocalFiniteMeasure.exhaustionCutoff_bounds K (index R) e.2).1
  have hFatou : (∫⁻ e, ENNReal.ofReal (f e.1) ∂(π : Measure (X × Y))) ≤
      atTop.liminf (fun R ↦ ENNReal.ofReal (LocalFiniteMeasure.testIntegral π
        (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R))))) := by
    calc
      _ = ∫⁻ e, atTop.liminf (fun R ↦ ENNReal.ofReal
          (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R)) e))
          ∂(π : Measure (X × Y)) := lintegral_congr fun e ↦ (hpt e).liminf_eq.symm
      _ ≤ atTop.liminf (fun R ↦ ∫⁻ e, ENNReal.ofReal
          (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R)) e)
          ∂(π : Measure (X × Y))) :=
        lintegral_liminf_le (fun R ↦
          (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R))).continuous.measurable.ennreal_ofReal)
      _ = _ := by
        apply congrArg (fun seq : ℕ → ℝ≥0∞ ↦ atTop.liminf seq)
        funext R
        exact (ofReal_integral_eq_lintegral_ofReal
          (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R))).integrable
          (Eventually.of_forall (hnonneg R))).symm
  have hcmp (R : ℕ) : ENNReal.ofReal (LocalFiniteMeasure.testIntegral π
      (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R)))) ≤
      A R + ENNReal.ofReal (LocalFiniteMeasure.testIntegral ν f) := by
    have hreal : LocalFiniteMeasure.testIntegral π
        (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R))) ≤
        |LocalFiniteMeasure.testIntegral ν f - LocalFiniteMeasure.testIntegral π
          (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R)))| +
          LocalFiniteMeasure.testIntegral ν f := by
      have := neg_le_abs (LocalFiniteMeasure.testIntegral ν f - LocalFiniteMeasure.testIntegral π
        (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K (index R))))
      linarith
    have hν : 0 ≤ LocalFiniteMeasure.testIntegral ν f := integral_nonneg hf
    simpa only [ENNReal.ofReal_add (abs_nonneg _) hν] using ENNReal.ofReal_le_ofReal hreal
  calc
    _ ≤ atTop.liminf (fun R ↦ A R + ENNReal.ofReal (LocalFiniteMeasure.testIntegral ν f)) :=
      hFatou.trans (liminf_le_liminf (Eventually.of_forall hcmp))
    _ = _ := by
      rw [liminf_add_const atTop A _ (by isBoundedDefault) (by isBoundedDefault)]
      rw [show atTop.liminf A = 0 from hzero, zero_add]

omit [SigmaCompactSpace X] [SigmaCompactSpace Y] in
/-- The exhaustion members of the countable error code themselves derive
local finiteness of the complete nonproper source projection. -/
theorem source_projection_finiteOnCompacts_of_liminf_cutoff_defects
    (π : LocalFiniteMeasure (X × Y)) (ν : LocalFiniteMeasure X)
    (KX : CompactExhaustion X) (KY : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion Y)
    (index : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℕ)
    (hindex : ∀ i, Tendsto (index i) atTop atTop)
    (hzero : ∀ j, atTop.liminf (fun R ↦ ENNReal.ofReal
      |LocalFiniteMeasure.testIntegral ν (LocalFiniteMeasure.separatingTest KX (.inl j)) -
        LocalFiniteMeasure.testIntegral π
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX (.inl j))
            (LocalFiniteMeasure.exhaustionCutoff (KY (.inl j)) (index (.inl j) R)))|) = 0) :
    IsFiniteMeasureOnCompacts (π : Measure (X × Y)).fst := by
  have hb (j : ℕ) : (π : Measure (X × Y)).fst (KX j) < ⊤ := by
    let f := LocalFiniteMeasure.exhaustionCutoff KX j
    have htest := lintegral_source_test_le_input_of_liminf_cutoff_defect_zero
      π ν f (fun x ↦ (LocalFiniteMeasure.exhaustionCutoff_bounds KX j x).1)
      (KY (.inl j)) (index (.inl j)) (hindex (.inl j)) (hzero j)
    have hm : (π : Measure (X × Y)).fst (KX j) ≤
        ∫⁻ e, ENNReal.ofReal (f e.1) ∂(π : Measure (X × Y)) := by
      let W : Set (X × Y) := Prod.fst ⁻¹' KX j
      have hW : MeasurableSet W := (KX.isCompact j).measurableSet.preimage measurable_fst
      calc
        _ = ∫⁻ e, W.indicator (fun _ ↦ (1 : ℝ≥0∞)) e ∂(π : Measure (X × Y)) := by
          exact (Measure.map_apply measurable_fst (KX.isCompact j).measurableSet).trans
            (lintegral_indicator_one hW).symm
        _ ≤ _ := lintegral_mono fun e ↦ by
          by_cases he : e ∈ W
          · rw [indicator_of_mem he]
            change 1 ≤ ENNReal.ofReal (LocalFiniteMeasure.exhaustionCutoff KX j e.1)
            have hx : LocalFiniteMeasure.exhaustionCutoff KX j e.1 = (1 : ℝ) :=
              LocalFiniteMeasure.exhaustionCutoff_eq_one KX j he
            rw [hx, ENNReal.ofReal_one]
          · rw [indicator_of_notMem he]
            exact zero_le
    exact (hm.trans htest).trans_lt ENNReal.ofReal_lt_top
  constructor
  intro K hK
  obtain ⟨j,hj⟩ := KX.exists_superset_of_isCompact hK
  exact (measure_mono hj).trans_lt (hb j)

/-- Exchange endpoints of an actual locally finite plan without altering its mass. -/
def LocalFiniteMeasure.swapEndpoints (π : LocalFiniteMeasure (X × Y)) :
    LocalFiniteMeasure (Y × X) :=
  ⟨(π : Measure (X × Y)).map Prod.swap,
    Measure.IsFiniteMeasureOnCompacts.map (π : Measure (X × Y)) (Homeomorph.prodComm X Y)⟩

/-- Endpoint exchange is continuous for the genuine compact-test topology. -/
theorem LocalFiniteMeasure.continuous_swapEndpoints :
    Continuous (LocalFiniteMeasure.swapEndpoints : LocalFiniteMeasure (X × Y) →
      LocalFiniteMeasure (Y × X)) := by
  apply LocalFiniteMeasure.isEmbedding_testIntegral.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro f
  let g : C_c(X × Y, ℝ) :=
    { toFun := fun e ↦ f e.swap
      continuous_toFun := f.continuous.comp continuous_swap
      hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (Homeomorph.prodComm X Y) }
  have heq : (fun π : LocalFiniteMeasure (X × Y) ↦
      LocalFiniteMeasure.testIntegral (LocalFiniteMeasure.swapEndpoints π) f) =
      fun π ↦ LocalFiniteMeasure.testIntegral π g := by
    funext π
    exact integral_map measurable_swap.aemeasurable f.continuous.aestronglyMeasurable
  exact heq ▸ LocalFiniteMeasure.continuous_testIntegral g

omit [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y] in
/-- Swapping a genuine compact product test swaps only its original endpoint factors. -/
theorem LocalFiniteMeasure.testIntegral_swapEndpoints_product
    (π : LocalFiniteMeasure (X × Y)) (f : C_c(Y, ℝ)) (g : C_c(X, ℝ)) :
    LocalFiniteMeasure.testIntegral (LocalFiniteMeasure.swapEndpoints π) (cavityProductTest f g) =
      LocalFiniteMeasure.testIntegral π (cavityProductTest g f) := by
  calc
    _ = ∫ e : X × Y, cavityProductTest f g e.swap ∂(π : Measure (X × Y)) :=
      integral_map measurable_swap.aemeasurable (cavityProductTest f g).continuous.aestronglyMeasurable
    _ = _ := integral_congr_ae (Eventually.of_forall fun e ↦ mul_comm _ _)

omit [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y] in
theorem LocalFiniteMeasure.swapEndpoints_fst (π : LocalFiniteMeasure (X × Y)) :
    (LocalFiniteMeasure.swapEndpoints π : Measure (Y × X)).fst = (π : Measure (X × Y)).snd :=
  Measure.fst_map_swap

omit [SigmaCompactSpace Y] in
/-- A genuine compact product cutoff recovers the source input of any actual
joint weak scene. The original finite readout error and actual partner escape
budget vanish independently; no optimizer, point-process law or full marginal
identity is built into the carrier. -/
theorem ae_source_input_marginal_eq_of_weak_readout_and_cutoff_errors
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (input : S → LocalFiniteMeasure X) (hinput : Continuous input)
    (KX : CompactExhaustion X) (KY : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion Y)
    (index : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℕ)
    (hindex : ∀ i, Tendsto (index i) atTop atTop)
    (originalError cutoffError : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞)
    (hOriginal : ∀ i, Tendsto (originalError i) atTop (𝓝 0))
    (hCutoff : ∀ i, Tendsto (cutoffError i) atTop (𝓝 0))
    (hbound : ∀ i R, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal
        |LocalFiniteMeasure.testIntegral (input s) (LocalFiniteMeasure.separatingTest KX i) -
          LocalFiniteMeasure.testIntegral (plan s)
            (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
              (LocalFiniteMeasure.exhaustionCutoff (KY i) (index i R)))| ∂(P n : Measure S)) ≤
        originalError i n + cutoffError i R) :
    ∀ᵐ s ∂(Q : Measure S), (plan s : Measure (X × Y)).fst = (input s : Measure X) := by
  let F := fun i R s ↦
    LocalFiniteMeasure.testIntegral (input s) (LocalFiniteMeasure.separatingTest KX i) -
      LocalFiniteMeasure.testIntegral (plan s)
        (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
          (LocalFiniteMeasure.exhaustionCutoff (KY i) (index i R)))
  have hF (i : ℕ ⊕ (ℕ × ℕ)) (R : ℕ) : Continuous (F i R) :=
    ((LocalFiniteMeasure.continuous_testIntegral _).comp hinput).sub
      ((LocalFiniteMeasure.continuous_testIntegral _).comp hplan)
  have hQbounds (i : ℕ ⊕ (ℕ × ℕ)) (R : ℕ) :
      (∫⁻ s, ENNReal.ofReal |F i R s| ∂(Q : Measure S)) ≤ cutoffError i R := by
    apply lintegral_abs_le_of_weak_eventual_tendsto_bound Q P hweak (F i R) (hF i R)
      (fun n ↦ originalError i n + cutoffError i R)
    · simpa only [zero_add] using (hOriginal i).add_const (cutoffError i R)
    · exact hbound i R
  have hzeroAll : ∀ᵐ s ∂(Q : Measure S), ∀ j : ℕ,
      atTop.liminf (fun R ↦ ENNReal.ofReal |F (.inl j) R s|) = 0 := by
    apply ae_all_iff.mpr
    intro j
    exact ae_liminf_abs_eq_zero_of_lintegral_bounds Q (F (.inl j)) (hF (.inl j))
      (cutoffError (.inl j)) (hCutoff (.inl j)) (hQbounds (.inl j))
  have hlocal : ∀ᵐ s ∂(Q : Measure S),
      IsFiniteMeasureOnCompacts (plan s : Measure (X × Y)).fst :=
    hzeroAll.mono fun s hs ↦ source_projection_finiteOnCompacts_of_liminf_cutoff_defects
      (plan s) (input s) KX KY index hindex hs
  have hall : ∀ᵐ s ∂(Q : Measure S), ∀ i : ℕ ⊕ (ℕ × ℕ),
      (∫ e, LocalFiniteMeasure.separatingTest KX i e.1 ∂(plan s : Measure (X × Y))) =
        LocalFiniteMeasure.testIntegral (input s) (LocalFiniteMeasure.separatingTest KX i) := by
    apply ae_all_iff.mpr
    intro i
    let f := LocalFiniteMeasure.separatingTest KX i
    let H := fun R s ↦ LocalFiniteMeasure.testIntegral (input s) f -
      LocalFiniteMeasure.testIntegral (plan s)
        (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff (KY i) (index i R)))
    have hH (R : ℕ) : Continuous (H R) :=
      ((LocalFiniteMeasure.continuous_testIntegral f).comp hinput).sub
        ((LocalFiniteMeasure.continuous_testIntegral _).comp hplan)
    have hQ (R : ℕ) : (∫⁻ s, ENNReal.ofReal |H R s| ∂(Q : Measure S)) ≤ cutoffError i R :=
      hQbounds i R
    have hzero := ae_eq_zero_of_weak_cutoff_errors Q (fun _ ↦ Q) tendsto_const_nhds
      H hH (cutoffError i) (hCutoff i) (fun R _ ↦ hQ R)
      (fun s ↦ LocalFiniteMeasure.testIntegral (input s) f -
        ∫ e, f e.1 ∂(plan s : Measure (X × Y))) (by
        filter_upwards [hlocal] with s hs
        let : IsFiniteMeasureOnCompacts ((plan s : Measure (X × Y)).map Prod.fst) := hs
        have hf : Integrable (fun e : X × Y ↦ f e.1) (plan s : Measure (X × Y)) :=
          (integrable_map_measure (f := Prod.fst) (g := fun x ↦ f x)
            f.continuous.aestronglyMeasurable measurable_fst.aemeasurable).mp f.integrable
        exact tendsto_const_nhds.sub ((tendsto_integral_cavityProductTest_cutoff
          (plan s : Measure (X × Y)) f (KY i) hf).comp (hindex i)))
    exact hzero.mono fun s hs ↦ (sub_eq_zero.mp hs).symm
  filter_upwards [hlocal, hall] with s hs htests
  let : IsFiniteMeasureOnCompacts ((plan s : Measure (X × Y)).map Prod.fst) := hs
  let projected : LocalFiniteMeasure X := ⟨(plan s : Measure (X × Y)).fst, hs⟩
  have heq : projected = input s := by
    apply LocalFiniteMeasure.separatingTestCode_injective KX
    funext i
    change (∫ x, LocalFiniteMeasure.separatingTest KX i x
      ∂(plan s : Measure (X × Y)).fst) = _
    rw [Measure.fst, integral_map
      (f := fun x ↦ LocalFiniteMeasure.separatingTest KX i x)
      measurable_fst.aemeasurable (LocalFiniteMeasure.separatingTest KX i).continuous.aestronglyMeasurable]
    exact htests i
  exact congrArg (fun m : LocalFiniteMeasure X ↦ (m : Measure X)) heq
/-- The same carrier-agnostic closure recovers the whole original target input;
source cutoff errors are removed by exchanging endpoints once. -/
theorem ae_target_input_marginal_eq_of_weak_readout_and_cutoff_errors
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (input : S → LocalFiniteMeasure Y) (hinput : Continuous input)
    (KY : CompactExhaustion Y) (KX : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion X)
    (index : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℕ)
    (hindex : ∀ i, Tendsto (index i) atTop atTop)
    (originalError cutoffError : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞)
    (hOriginal : ∀ i, Tendsto (originalError i) atTop (𝓝 0))
    (hCutoff : ∀ i, Tendsto (cutoffError i) atTop (𝓝 0))
    (hbound : ∀ i R, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal
        |LocalFiniteMeasure.testIntegral (input s) (LocalFiniteMeasure.separatingTest KY i) -
          LocalFiniteMeasure.testIntegral (plan s)
            (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (KX i) (index i R))
              (LocalFiniteMeasure.separatingTest KY i))| ∂(P n : Measure S)) ≤
        originalError i n + cutoffError i R) :
    ∀ᵐ s ∂(Q : Measure S), (plan s : Measure (X × Y)).snd = (input s : Measure Y) := by
  have hswap : Continuous (fun s ↦ LocalFiniteMeasure.swapEndpoints (plan s)) :=
    LocalFiniteMeasure.continuous_swapEndpoints.comp hplan
  have hb : ∀ i R, ∀ᶠ n in atTop,
      (∫⁻ s, ENNReal.ofReal
        |LocalFiniteMeasure.testIntegral (input s) (LocalFiniteMeasure.separatingTest KY i) -
          LocalFiniteMeasure.testIntegral (LocalFiniteMeasure.swapEndpoints (plan s))
            (cavityProductTest (LocalFiniteMeasure.separatingTest KY i)
              (LocalFiniteMeasure.exhaustionCutoff (KX i) (index i R)))| ∂(P n : Measure S)) ≤
        originalError i n + cutoffError i R := by
    simpa only [LocalFiniteMeasure.testIntegral_swapEndpoints_product] using hbound
  have h := ae_source_input_marginal_eq_of_weak_readout_and_cutoff_errors Q P hweak
    (fun s ↦ LocalFiniteMeasure.swapEndpoints (plan s)) hswap input hinput
    KY KX index hindex originalError cutoffError hOriginal hCutoff hb
  simpa only [LocalFiniteMeasure.swapEndpoints_fst] using h
end Marginal
end OTSelector.Probability
