import OTSelector.Reconstruction.MarkedStationaryValueLegalInputColorMarginals
import OTSelector.MeasureTheory.WeakInputMarginals

/-!
# Full original-input marginals from a common cutoff budget

## Conditions
The prescribed probability laws converge weakly. Every original compact input
readout has a vanishing finite-scene error, and genuine compact partner cutoffs
make its remaining expected defect arbitrarily small.

## Objects
`plan` is the continuous oriented plan projection of the same legal input scene;
`color` selects the unchanged original input. Exchanging endpoints in `plan`
gives the target statement without reversing the legal matching graph.

## Proof
Choose one exhaustion cutoff for each countable separating test and tolerance.
The existing `WeakInputMarginals` closure transfers its finite bound through the
weak limit and identifies the complete marginal. The mathematical background
is the Portmanteau, Fatou and compact-test separation infrastructure documented
in `OTSelector.Probability.WeakInputMarginals`.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance (q : ℕ) : PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) :=
  LocalFiniteMeasure.instPolishSpace
local instance (q : ℕ) : PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace

/-- A common compact-cutoff budget recovers one unchanged input color on its
actual weak scene law. All original error and escape estimates are supplied by
the caller; the limiting marginal is a conclusion. -/
theorem ae_legalMarkedInput_marginal_eq_of_cutoff_budgets
    (q : ℕ) (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (P : ℕ → ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hweak : Tendsto P atTop (𝓝 Q))
    (plan : LegalMarkedOptimalInputScene q → LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (hplan : Continuous plan) (color : Fin 2)
    (error : C_c(LegalMarkedPhysicalPoint q, ℝ) → ℕ → ℝ≥0∞)
    (herror : ∀ f, Tendsto (error f) atTop (𝓝 0))
    (hbudget : ∀ f : C_c(LegalMarkedPhysicalPoint q, ℝ), ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ T : Set (LegalMarkedPhysicalPoint q), IsCompact T ∧
        ∀ χ : C_c(LegalMarkedPhysicalPoint q, ℝ), (∀ x, χ x ∈ Icc 0 1) → EqOn χ 1 T →
          ∀ᶠ n in atTop,
            (∫⁻ s, ENNReal.ofReal
              |LocalFiniteMeasure.testIntegral s.2 (cavityProductTest f (legalInputColorTest color)) -
                LocalFiniteMeasure.testIntegral (plan s) (cavityProductTest f χ)|
                ∂(P n : Measure (LegalMarkedOptimalInputScene q))) ≤
              error f n + ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ * ε) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (plan s : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 color := by
  let E := CompactExhaustion.choice (LegalMarkedPhysicalPoint q)
  let input : LegalMarkedOptimalInputScene q → LocalFiniteMeasure (LegalMarkedPhysicalPoint q) :=
    fun s ↦ ⟨legalInputColorMeasure q s.2 color, inferInstance⟩
  have hinput : Continuous input := by
    apply LocalFiniteMeasure.isEmbedding_testIntegral.isInducing.continuous_iff.mpr
    apply continuous_pi
    intro f
    have heq : (fun s ↦ LocalFiniteMeasure.testIntegral (input s) f) =
        fun s : LegalMarkedOptimalInputScene q ↦
          LocalFiniteMeasure.testIntegral s.2 (cavityProductTest f (legalInputColorTest color)) := by
      funext s
      exact integral_legalInputColorMeasure q s.2 color f
    change Continuous (fun s ↦ LocalFiniteMeasure.testIntegral (input s) f)
    rw [heq]
    exact (LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd
  let eps (R : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((R : ℝ) + 1))
  have heps (R : ℕ) : 0 < eps R := ENNReal.ofReal_pos.mpr (by positivity)
  have hepslim : Tendsto eps atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose T hT hbound using fun i R ↦ hbudget (LocalFiniteMeasure.separatingTest E i) (eps R) (heps R)
  choose j hj using fun i R ↦ E.exists_superset_of_isCompact (hT i R)
  let index (i : ℕ ⊕ (ℕ × ℕ)) (R : ℕ) := max R (j i R)
  have hindex (i : ℕ ⊕ (ℕ × ℕ)) : Tendsto (index i) atTop atTop :=
    tendsto_atTop_mono (fun R ↦ le_max_left R (j i R)) tendsto_id
  apply ae_source_input_marginal_eq_of_weak_readout_and_cutoff_errors Q P hweak plan hplan
    input hinput E (fun _ ↦ E) index hindex
    (fun i ↦ error (LocalFiniteMeasure.separatingTest E i))
    (fun i R ↦ ENNReal.ofReal ‖(LocalFiniteMeasure.separatingTest E i).toBoundedContinuousFunction‖ * eps R)
    (fun i ↦ herror (LocalFiniteMeasure.separatingTest E i))
    (fun i ↦ by simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hepslim (Or.inr ENNReal.ofReal_ne_top))
  intro i R
  have hgT : EqOn (LocalFiniteMeasure.exhaustionCutoff E (index i R)) 1 (T i R) := by
    intro x hx
    exact LocalFiniteMeasure.exhaustionCutoff_eq_one E (index i R)
      (E.subset (le_max_right R (j i R)) (hj i R hx))
  have h := hbound i R _ (LocalFiniteMeasure.exhaustionCutoff_bounds E (index i R)) hgT
  simpa only [input, LocalFiniteMeasure.testIntegral, integral_legalInputColorMeasure] using h

end OTSelector.Reconstruction
