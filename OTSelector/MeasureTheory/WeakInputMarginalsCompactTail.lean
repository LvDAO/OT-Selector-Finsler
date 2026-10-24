import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Probability.Kernel.Basic
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
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import OTSelector.MeasureTheory.WeakInputMarginals

/-!
## Lemma skeleton

* **Conditions:** Finite-scene readout convergence and compact partner tails, with joint weak convergence.
* **Objects:** A cutoff schedule proving full limiting input marginals.
* **Proof detail:** Choose compact cutoffs from the tail hypothesis and instantiate weak marginal closure.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=68
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf

**Relationship to the sources:** The schedule is derived from the actual tails; the references supply weak convergence and compactness, while this combined criterion is proved locally.
-/

/-!
# Full weak-scene input marginals from original readouts and compact partner tails

The cutoff schedule is chosen from the actual finite-scene compact-tail bound.
No projected local finiteness or limiting marginal identity is supplied.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {X Y S : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
  [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
  [SecondCountableTopology Y]
  [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- A genuine vanishing full input readout error and actual compact partner tails
force the complete source marginal on the prescribed weak scene law. The finite
plans are only required to be finite almost surely at each original index. -/
theorem ae_source_input_marginal_eq_of_weak_readout_and_compact_tails
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (input : S → LocalFiniteMeasure X) (hinput : Continuous input)
    (hfinite : ∀ n, ∀ᵐ s ∂(P n : Measure S), IsFiniteMeasure (plan s : Measure (X × Y)))
    (KX : CompactExhaustion X) (KY : CompactExhaustion Y)
    (hOriginal : ∀ i : ℕ ⊕ (ℕ × ℕ), Tendsto (fun n ↦
      ∫⁻ s, ENNReal.ofReal
        |LocalFiniteMeasure.testIntegral (input s) (LocalFiniteMeasure.separatingTest KX i) -
          ∫ e, LocalFiniteMeasure.separatingTest KX i e.1
            ∂(plan s : Measure (X × Y))| ∂(P n : Measure S)) atTop (𝓝 0))
    (htail : ∀ i : ℕ ⊕ (ℕ × ℕ), ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ K : Set Y, IsCompact K ∧ ∀ᶠ n in atTop,
        (∫⁻ s, (plan s : Measure (X × Y))
          (tsupport (LocalFiniteMeasure.separatingTest KX i) ×ˢ Kᶜ)
          ∂(P n : Measure S)) ≤ ε) :
    ∀ᵐ s ∂(Q : Measure S), (plan s : Measure (X × Y)).fst = (input s : Measure X) := by
  let eps : ℕ → ℝ≥0∞ := fun R ↦ ENNReal.ofReal (1 / ((R : ℝ) + 1))
  have heps (R : ℕ) : 0 < eps R := by dsimp [eps]; positivity
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps, Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  choose K hK htailK using fun i R ↦ htail i (eps R) (heps R)
  choose j hj using fun i R ↦ KY.exists_superset_of_isCompact (hK i R)
  let index : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℕ := fun i R ↦ max R (j i R)
  have hindex (i : ℕ ⊕ (ℕ × ℕ)) : Tendsto (index i) atTop atTop :=
    tendsto_atTop_mono (fun R ↦ le_max_left R (j i R)) tendsto_id
  let originalError : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞ := fun i n ↦
    ∫⁻ s, ENNReal.ofReal
      |LocalFiniteMeasure.testIntegral (input s) (LocalFiniteMeasure.separatingTest KX i) -
        ∫ e, LocalFiniteMeasure.separatingTest KX i e.1
          ∂(plan s : Measure (X × Y))| ∂(P n : Measure S)
  let cutoffError : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞ := fun i R ↦
    ENNReal.ofReal ‖(LocalFiniteMeasure.separatingTest KX i).toBoundedContinuousFunction‖ * eps R
  have hCutoff (i : ℕ ⊕ (ℕ × ℕ)) : Tendsto (cutoffError i) atTop (𝓝 0) := by
    simpa only [cutoffError, mul_zero] using
      ENNReal.Tendsto.const_mul heps0 (Or.inr ENNReal.ofReal_ne_top)
  apply ae_source_input_marginal_eq_of_weak_readout_and_cutoff_errors Q P hweak
    plan hplan input hinput KX (fun _ ↦ KY) index hindex originalError cutoffError
    hOriginal hCutoff
  intro i R
  filter_upwards [htailK i R] with n hn
  let f := LocalFiniteMeasure.separatingTest KX i
  let g := LocalFiniteMeasure.exhaustionCutoff KY (index i R)
  have hgK : EqOn g 1 (K i R) := by
    intro y hy
    exact LocalFiniteMeasure.exhaustionCutoff_eq_one KY (index i R)
      (KY.subset (le_max_right R (j i R)) (hj i R hy))
  have hpoint : ∀ᵐ s ∂(P n : Measure S),
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral (input s) f -
        LocalFiniteMeasure.testIntegral (plan s) (cavityProductTest f g)| ≤
      ENNReal.ofReal |LocalFiniteMeasure.testIntegral (input s) f -
        ∫ e, f e.1 ∂(plan s : Measure (X × Y))| +
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (plan s : Measure (X × Y)) (tsupport f ×ˢ (K i R)ᶜ) := by
    filter_upwards [hfinite n] with s hs
    let : IsFiniteMeasure (plan s : Measure (X × Y)) := hs
    exact ofReal_abs_input_sub_product_le_full_error_tail (plan s : Measure (X × Y))
      (input s) f g (LocalFiniteMeasure.exhaustionCutoff_bounds KY (index i R)) (K i R) hgK
  have hmeasure : Measurable (fun s ↦ (plan s : Measure (X × Y))) :=
    Reconstruction.measurable_localFiniteMeasure_coe.comp hplan.measurable
  have htailm : Measurable (fun s ↦
      (plan s : Measure (X × Y)) (tsupport f ×ˢ (K i R)ᶜ)) :=
    (Measure.measurable_coe ((isClosed_tsupport f).measurableSet.prod
      (hK i R).isClosed.measurableSet.compl)).comp hmeasure
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal |LocalFiniteMeasure.testIntegral (input s) f -
        ∫ e, f e.1 ∂(plan s : Measure (X × Y))| +
        ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
          (plan s : Measure (X × Y)) (tsupport f ×ˢ (K i R)ᶜ)
        ∂(P n : Measure S) := lintegral_mono_ae hpoint
    _ = originalError i n + ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        (∫⁻ s, (plan s : Measure (X × Y)) (tsupport f ×ˢ (K i R)ᶜ)
          ∂(P n : Measure S)) := by
      have hadd := lintegral_add_right (μ := (P n : Measure S))
        (fun s ↦ ENNReal.ofReal |LocalFiniteMeasure.testIntegral (input s) f -
          ∫ e, f e.1 ∂(plan s : Measure (X × Y))|)
        (show Measurable (fun s ↦ ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
          (plan s : Measure (X × Y)) (tsupport f ×ˢ (K i R)ᶜ)) from
          measurable_const.mul htailm)
      exact hadd.trans (congrArg (fun v ↦ originalError i n + v)
        (lintegral_const_mul _ htailm))
    _ ≤ originalError i n + cutoffError i R :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hn zero_le)

/-- The same original finite-scene readout and compact-tail criterion recovers
all target mass on its prescribed weak law by exchanging the actual endpoints. -/
theorem ae_target_input_marginal_eq_of_weak_readout_and_compact_tails
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (input : S → LocalFiniteMeasure Y) (hinput : Continuous input)
    (hfinite : ∀ n, ∀ᵐ s ∂(P n : Measure S), IsFiniteMeasure (plan s : Measure (X × Y)))
    (KY : CompactExhaustion Y) (KX : CompactExhaustion X)
    (hOriginal : ∀ i : ℕ ⊕ (ℕ × ℕ), Tendsto (fun n ↦
      ∫⁻ s, ENNReal.ofReal
        |LocalFiniteMeasure.testIntegral (input s) (LocalFiniteMeasure.separatingTest KY i) -
          ∫ e, LocalFiniteMeasure.separatingTest KY i e.2
            ∂(plan s : Measure (X × Y))| ∂(P n : Measure S)) atTop (𝓝 0))
    (htail : ∀ i : ℕ ⊕ (ℕ × ℕ), ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ K : Set X, IsCompact K ∧ ∀ᶠ n in atTop,
        (∫⁻ s, (plan s : Measure (X × Y))
          (Kᶜ ×ˢ tsupport (LocalFiniteMeasure.separatingTest KY i))
          ∂(P n : Measure S)) ≤ ε) :
    ∀ᵐ s ∂(Q : Measure S), (plan s : Measure (X × Y)).snd = (input s : Measure Y) := by
  have hswap : Continuous (fun s ↦ LocalFiniteMeasure.swapEndpoints (plan s)) :=
    LocalFiniteMeasure.continuous_swapEndpoints.comp hplan
  have hfin : ∀ n, ∀ᵐ s ∂(P n : Measure S),
      IsFiniteMeasure (LocalFiniteMeasure.swapEndpoints (plan s) : Measure (Y × X)) := by
    intro n
    filter_upwards [hfinite n] with s hs
    let : IsFiniteMeasure (plan s : Measure (X × Y)) := hs
    change IsFiniteMeasure ((plan s : Measure (X × Y)).map Prod.swap)
    infer_instance
  have hfull (s : S) (f : C_c(Y, ℝ)) :
      (∫ e, f e.1 ∂(LocalFiniteMeasure.swapEndpoints (plan s) : Measure (Y × X))) =
        ∫ e, f e.2 ∂(plan s : Measure (X × Y)) := by
    change (∫ e, f e.1 ∂((plan s : Measure (X × Y)).map Prod.swap)) = _
    exact integral_map (f := fun e : Y × X ↦ f e.1) measurable_swap.aemeasurable
      (f.continuous.comp continuous_fst).aestronglyMeasurable
  have h := ae_source_input_marginal_eq_of_weak_readout_and_compact_tails Q P hweak
    (fun s ↦ LocalFiniteMeasure.swapEndpoints (plan s)) hswap input hinput hfin KY KX
    (by simpa only [hfull] using hOriginal) (by
      intro i ε hε
      obtain ⟨K, hK, hbound⟩ := htail i ε hε
      refine ⟨K, hK, ?_⟩
      have heq (s : S) :
          (LocalFiniteMeasure.swapEndpoints (plan s) : Measure (Y × X))
            (tsupport (LocalFiniteMeasure.separatingTest KY i) ×ˢ Kᶜ) =
          (plan s : Measure (X × Y))
            (Kᶜ ×ˢ tsupport (LocalFiniteMeasure.separatingTest KY i)) := by
        change ((plan s : Measure (X × Y)).map Prod.swap) _ = _
        rw [Measure.map_apply measurable_swap
          ((isClosed_tsupport _).measurableSet.prod hK.isClosed.measurableSet.compl)]
        congr 1
        ext e
        exact and_comm
      simpa only [heq] using hbound)
  simpa only [LocalFiniteMeasure.swapEndpoints_fst] using h

end OTSelector.Probability
