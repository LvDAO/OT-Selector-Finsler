import LeanPool.Vlasov.OT.Coupling
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Transport.Coupling.MixtureLabelTransfer

## Lemma skeleton

* **Conditions:** Finite families of finite component measures and a coupling of their sums; the label-matrix normalization specializes to probability components.

* **Objects:** RN-weighted coupling parts and the induced finite label coupling with exact row/column marginals.

* **Proof detail:** Each component is dominated by the finite mixture. Its RN derivative supplies a measurable weight, and the derivatives sum to one almost everywhere. Weight the original coupling by the product of the endpoint RN weights, then sum and project to recover each original component.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=144): Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144.

Source relation (composition): Local label-transfer construction from RN derivatives; it does not require disjoint component supports or a chosen label map for points in overlapping components.
-/

/-! A continuous coupling of finite labelled mixtures induces an actual coupling
of the original labels, with the literal quadratic displacement estimate. -/
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1600000
variable {X Y I J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype I] [Fintype J]

private lemma finiteMixture_component_le (κ : I → Measure X) (i : I) :
    κ i ≤ ∑ k, κ k := by
  classical
  exact Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i)

/-- The actual Radon--Nikodym label probabilities form a partition of unity,
even when some component measures or the entire mixture vanish. -/
theorem finiteMixture_rnDeriv_sum (κ : I → Measure X) [∀ i, IsFiniteMeasure (κ i)] :
    (fun z ↦ ∑ i, (κ i).rnDeriv (∑ k, κ k) z) =ᵐ[∑ k, κ k] fun _ ↦ 1 := by
  classical
  let μ := ∑ k, κ k
  have hm (i : I) : κ i ≪ μ := (finiteMixture_component_le κ i).absolutelyContinuous
  have hsum : μ.withDensity (fun z ↦ ∑ i, (κ i).rnDeriv μ z) = μ := by
    have ht := withDensity_tsum (μ := μ) (fun i : I ↦ Measure.measurable_rnDeriv (κ i) μ)
    simp only [tsum_fintype, Measure.sum_fintype, Finset.sum_fn] at ht
    rw [ht]
    simp_rw [Measure.withDensity_rnDeriv_eq _ _ (hm _)]
    rfl
  apply (withDensity_eq_iff_of_sigmaFinite
    (Finset.measurable_sum _ (fun i _ ↦ Measure.measurable_rnDeriv (κ i) μ)).aemeasurable
    measurable_const.aemeasurable).mp
  simpa only [withDensity_const, one_smul] using hsum

/-- The genuine part of a continuous mixture coupling carrying the specified
source and target labels. Overlap of smoothing supports is allowed. -/
def smoothingEndpointCouplingPart (κ : I → Measure X) (σ : J → Measure Y)
    (π : Measure (X × Y)) (i : I) (j : J) : Measure (X × Y) :=
  π.withDensity (fun z ↦ (κ i).rnDeriv (∑ k, κ k) z.1 *
    (σ j).rnDeriv (∑ k, σ k) z.2)

private lemma finite_withDensity_sum (μ : Measure X) (f : I → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    μ.withDensity (fun z ↦ ∑ i, f i z) = ∑ i, μ.withDensity (f i) := by
  have ht := withDensity_tsum (μ := μ) hf
  simpa only [tsum_fintype, Measure.sum_fintype, Finset.sum_fn] using ht

/-- Summing every actual label part restores the prescribed continuous coupling. -/
theorem smoothingEndpointCouplingPart_sum (κ : I → Measure X) (σ : J → Measure Y)
    [∀ i, IsFiniteMeasure (κ i)] [∀ j, IsFiniteMeasure (σ j)]
    (π : Measure (X × Y)) (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j)) :
    ∑ i, ∑ j, smoothingEndpointCouplingPart κ σ π i j = π := by
  classical
  have hκ := finiteMixture_rnDeriv_sum κ
  have hσ := finiteMixture_rnDeriv_sum σ
  have hκ' : ∀ᵐ z : X × Y ∂π, ∑ i, (κ i).rnDeriv (∑ k, κ k) z.1 = 1 := by
    apply ae_of_ae_map (μ := π) (p := fun z ↦ ∑ i, (κ i).rnDeriv (∑ k, κ k) z = 1) measurable_fst.aemeasurable
    simpa only [hπ.1, Filter.EventuallyEq] using hκ
  have hσ' : ∀ᵐ z : X × Y ∂π, ∑ j, (σ j).rnDeriv (∑ k, σ k) z.2 = 1 := by
    apply ae_of_ae_map (μ := π) (p := fun z ↦ ∑ j, (σ j).rnDeriv (∑ k, σ k) z = 1) measurable_snd.aemeasurable
    simpa only [hπ.2, Filter.EventuallyEq] using hσ
  have hsum : (fun z : X × Y ↦ ∑ i, ∑ j,
      (κ i).rnDeriv (∑ k, κ k) z.1 * (σ j).rnDeriv (∑ k, σ k) z.2) =ᵐ[π] fun _ ↦ 1 := by
    filter_upwards [hκ', hσ'] with z hzκ hzσ
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hzκ, hzσ, one_mul]
  calc
    _ = π.withDensity (fun z ↦ ∑ i, ∑ j,
      (κ i).rnDeriv (∑ k, κ k) z.1 * (σ j).rnDeriv (∑ k, σ k) z.2) := by
        rw [finite_withDensity_sum _ _ (by intro i; fun_prop)]
        apply Finset.sum_congr rfl
        intro i _
        rw [finite_withDensity_sum _ _ (by
          intro j
          exact ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul
            ((Measure.measurable_rnDeriv _ _).comp measurable_snd))]
        rfl
    _ = π := by rw [withDensity_congr_ae hsum, withDensity_const, one_smul]

private lemma map_withDensity_comp {f : X → Y} (hf : Measurable f)
    (μ : Measure X) {g : Y → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hf hs), ← lintegral_indicator hs,
    lintegral_map (hg.indicator hs) hf]
  rfl

/-- The first marginal of each genuine source-labelled row is its original
smoothing measure, without a disjointness requirement on the mixture. -/
theorem smoothingEndpointCouplingPart_row (κ : I → Measure X) (σ : J → Measure Y)
    [∀ i, IsFiniteMeasure (κ i)] [∀ j, IsFiniteMeasure (σ j)]
    (π : Measure (X × Y)) (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j)) (i : I) :
    (∑ j, smoothingEndpointCouplingPart κ σ π i j).map Prod.fst = κ i := by
  classical
  have hσ' : ∀ᵐ z : X × Y ∂π, ∑ j, (σ j).rnDeriv (∑ k, σ k) z.2 = 1 := by
    apply ae_of_ae_map (μ := π) (p := fun z ↦ ∑ j, (σ j).rnDeriv (∑ k, σ k) z = 1)
      measurable_snd.aemeasurable
    simpa only [hπ.2, Filter.EventuallyEq] using finiteMixture_rnDeriv_sum σ
  have hsum : (fun z : X × Y ↦ ∑ j,
      (κ i).rnDeriv (∑ k, κ k) z.1 * (σ j).rnDeriv (∑ k, σ k) z.2) =ᵐ[π]
      (κ i).rnDeriv (∑ k, κ k) ∘ Prod.fst := by
    filter_upwards [hσ'] with z hz
    simp only [← Finset.mul_sum, hz, mul_one, Function.comp_apply]
  have hrow : ∑ j, smoothingEndpointCouplingPart κ σ π i j =
      π.withDensity ((κ i).rnDeriv (∑ k, κ k) ∘ Prod.fst) := by
    rw [← withDensity_congr_ae hsum, finite_withDensity_sum _ _ (by
      intro j
      exact ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul
        ((Measure.measurable_rnDeriv _ _).comp measurable_snd))]
    rfl
  rw [hrow, map_withDensity_comp measurable_fst _ (Measure.measurable_rnDeriv _ _), hπ.1]
  exact Measure.withDensity_rnDeriv_eq _ _ (finiteMixture_component_le κ i).absolutelyContinuous

/-- The second marginal of each genuine target-labelled column is its original
smoothing measure. -/
theorem smoothingEndpointCouplingPart_column (κ : I → Measure X) (σ : J → Measure Y)
    [∀ i, IsFiniteMeasure (κ i)] [∀ j, IsFiniteMeasure (σ j)]
    (π : Measure (X × Y)) (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j)) (j : J) :
    (∑ i, smoothingEndpointCouplingPart κ σ π i j).map Prod.snd = σ j := by
  classical
  have hκ' : ∀ᵐ z : X × Y ∂π, ∑ i, (κ i).rnDeriv (∑ k, κ k) z.1 = 1 := by
    apply ae_of_ae_map (μ := π) (p := fun z ↦ ∑ i, (κ i).rnDeriv (∑ k, κ k) z = 1)
      measurable_fst.aemeasurable
    simpa only [hπ.1, Filter.EventuallyEq] using finiteMixture_rnDeriv_sum κ
  have hsum : (fun z : X × Y ↦ ∑ i,
      (κ i).rnDeriv (∑ k, κ k) z.1 * (σ j).rnDeriv (∑ k, σ k) z.2) =ᵐ[π]
      (σ j).rnDeriv (∑ k, σ k) ∘ Prod.snd := by
    filter_upwards [hκ'] with z hz
    simp only [← Finset.sum_mul, hz, one_mul, Function.comp_apply]
  have hcol : ∑ i, smoothingEndpointCouplingPart κ σ π i j =
      π.withDensity ((σ j).rnDeriv (∑ k, σ k) ∘ Prod.snd) := by
    rw [← withDensity_congr_ae hsum, finite_withDensity_sum _ _ (by
      intro i
      exact ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul
        ((Measure.measurable_rnDeriv _ _).comp measurable_snd))]
    rfl
  rw [hcol, map_withDensity_comp measurable_snd _ (Measure.measurable_rnDeriv _ _), hπ.2]
  exact Measure.withDensity_rnDeriv_eq _ _ (finiteMixture_component_le σ j).absolutelyContinuous

/-- Each labelled part is a genuine submeasure of the prescribed coupling. -/
theorem smoothingEndpointCouplingPart_le (κ : I → Measure X) (σ : J → Measure Y)
    [∀ i, IsFiniteMeasure (κ i)] [∀ j, IsFiniteMeasure (σ j)]
    (π : Measure (X × Y)) (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j)) (i : I) (j : J) :
    smoothingEndpointCouplingPart κ σ π i j ≤ π := by
  classical
  calc
    _ ≤ ∑ k, ∑ l, smoothingEndpointCouplingPart κ σ π k l :=
      (Finset.single_le_sum (f := fun l ↦ smoothingEndpointCouplingPart κ σ π i l)
        (fun _ _ ↦ bot_le) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun k ↦ ∑ l, smoothingEndpointCouplingPart κ σ π k l)
          (fun _ _ ↦ bot_le) (Finset.mem_univ i))
    _ = π := smoothingEndpointCouplingPart_sum κ σ π hπ

/-- The actual label matrix records the masses of the Radon--Nikodym parts. -/
def smoothingEndpointLabelMatrix (κ : I → Measure X) (σ : J → Measure Y)
    (π : Measure (X × Y)) (i : I) (j : J) : ℝ :=
  (smoothingEndpointCouplingPart κ σ π i j).real univ

/-- Probability smoothing components give exact unit rows and columns. -/
theorem smoothingEndpointLabelMatrix_rows_columns (κ : I → Measure X) (σ : J → Measure Y)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (σ j)]
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j)) :
    (∀ i j, 0 ≤ smoothingEndpointLabelMatrix κ σ π i j) ∧
    (∀ i, ∑ j, smoothingEndpointLabelMatrix κ σ π i j = 1) ∧
    (∀ j, ∑ i, smoothingEndpointLabelMatrix κ σ π i j = 1) := by
  classical
  have hfinite (i : I) (j : J) : smoothingEndpointCouplingPart κ σ π i j univ ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top π univ)
      (Measure.le_iff'.mp (smoothingEndpointCouplingPart_le κ σ π hπ i j) univ)
  refine ⟨fun _ _ ↦ ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro i
    have hr := congrArg (fun μ : Measure X ↦ μ univ)
      (smoothingEndpointCouplingPart_row κ σ π hπ i)
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, Measure.finsetSum_apply,
      show κ i univ = 1 from measure_univ] at hr
    have := congrArg ENNReal.toReal hr
    simpa only [ENNReal.toReal_sum (fun j _ ↦ hfinite i j), ENNReal.toReal_one,
      smoothingEndpointLabelMatrix, measureReal_def] using this
  · intro j
    have hc := congrArg (fun μ : Measure Y ↦ μ univ)
      (smoothingEndpointCouplingPart_column κ σ π hπ j)
    rw [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ, Measure.finsetSum_apply,
      show σ j univ = 1 from measure_univ] at hc
    have := congrArg ENNReal.toReal hc
    simpa only [ENNReal.toReal_sum (fun i _ ↦ hfinite i j), ENNReal.toReal_one,
      smoothingEndpointLabelMatrix, measureReal_def] using this

end OTSelector.Reconstruction
