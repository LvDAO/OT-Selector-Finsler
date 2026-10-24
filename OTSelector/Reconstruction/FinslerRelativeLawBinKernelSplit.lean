import OTSelector.Probability.BinnedPopulation
import OTSelector.Probability.CellwisePopulation

/-!
Actual normalized original clock bins restore literal conditional marginals at
every covered label. A legal retained/residual finite flow gives continuous
pair kernels with exact original marginals and the same quantitative residual
mass bound, even when empty-bin fallback laws are arbitrary.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The literal original clock marginal is restored at every label where the
actual finite bins cover its support. Empty-bin fallback laws cancel exactly. -/
theorem finiteClassMarginalKernel_normalized_bins_eq_original_at
    {I Z X : Type*} [Fintype I] [MeasurableSpace Z] [MeasurableSpace X]
    (κ : Kernel Z X) [IsSFiniteKernel κ] [∀ z, IsFiniteMeasure (κ z)]
    (B : I → Set X) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (fallback : I → X)
    (z : Z) (hcover : ∀ᵐ x ∂κ z, x ∈ ⋃ i, B i) :
    finiteClassMarginalKernel (fun w i ↦ (κ w).real (B i))
      (fun i ↦ normalizedActualBinKernel κ (B i) (hB i) (fallback i)) z = κ z := by
  classical
  have hm (i : I) : Measurable (fun w ↦ (κ w).real (B i)) :=
    (κ.measurable_coe (hB i)).ennreal_toReal
  rw [finiteClassMarginalKernel_apply _ hm]
  simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    binMass_smul_normalizedActualBinKernel]
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hB]
  exact Measure.restrict_eq_self_of_ae_mem hcover

/-- A local original-bin reference split supplies the continuous pair-kernel
interface used by cellwise physical reconstruction, with its actual mass bound. -/
theorem originalBinPairKernel_split_at
    {I J Z : Type*} [Fintype I] [Fintype J] [MeasurableSpace Z]
    (κ₀ κ₁ : Kernel Z ℝ) [IsMarkovKernel κ₀] [IsMarkovKernel κ₁]
    (S : I → Set ℝ) (T : J → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (fallbackS : I → ℝ) (fallbackT : J → ℝ)
    (P Q : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (allowed : I → J → Prop)
    (hbins : ∀ i j, allowed i j → ∀ s ∈ S i, ∀ t ∈ T j, s ≤ t)
    (z : Z)
    (hcoverS : ∀ᵐ s ∂κ₀ z, s ∈ ⋃ i, S i)
    (hcoverT : ∀ᵐ t ∂κ₁ z, t ∈ ⋃ j, T j)
    (hP : ∀ i j, 0 ≤ P z i j) (hQ : ∀ i j, 0 ≤ Q z i j)
    (hrow : ∀ i, ∑ j, (P z i j + Q z i j) = (κ₀ z).real (S i))
    (hcol : ∀ j, ∑ i, (P z i j + Q z i j) = (κ₁ z).real (T j))
    (hzero : ∀ i j, ¬ allowed i j → P z i j = 0 ∧ Q z i j = 0)
    (B : ℝ) (hmass : (∑ i, ∑ j, Q z i j) ≤ B) :
    let α := fun i ↦ normalizedActualBinKernel κ₀ (S i) (hS i) (fallbackS i)
    let β := fun j ↦ normalizedActualBinKernel κ₁ (T j) (hT j) (fallbackT j)
    let KP := finiteClassPopulationKernel P α β
    let KQ := finiteClassPopulationKernel Q α β
    Vlasov.IsCoupling (KP z + KQ z) (κ₀ z) (κ₁ z) ∧
      (∀ᵐ p ∂KP z + KQ z, p.1 ≤ p.2) ∧ KQ z univ ≤ ENNReal.ofReal B := by
  classical
  let α := fun i ↦ normalizedActualBinKernel κ₀ (S i) (hS i) (fallbackS i)
  let β := fun j ↦ normalizedActualBinKernel κ₁ (T j) (hT j) (fallbackT j)
  let asrc := fun w i ↦ (κ₀ w).real (S i)
  let btgt := fun w j ↦ (κ₁ w).real (T j)
  let W := fun w i j ↦ P w i j + Q w i j
  have hW : ∀ i j, 0 ≤ W z i j := fun i j ↦ add_nonneg (hP i j) (hQ i j)
  have hmW (i : I) (j : J) : Measurable (fun w ↦ W w i j) :=
    measurable_add.comp ((hmP i j).prodMk (hmQ i j))
  have hma (i : I) : Measurable (fun w ↦ asrc w i) := (κ₀.measurable_coe (hS i)).ennreal_toReal
  have hmb (j : J) : Measurable (fun w ↦ btgt w j) := (κ₁.measurable_coe (hT j)).ennreal_toReal
  have hsplit : finiteClassPopulationKernel P α β z + finiteClassPopulationKernel Q α β z =
      finiteClassPopulationCoupling (W z) (fun i ↦ α i z) (fun j ↦ β j z) := by
    rw [finiteClassPopulationKernel_apply _ hmP, finiteClassPopulationKernel_apply _ hmQ]
    exact (finiteClassPopulationCoupling_add _ _ _ _ hP hQ).symm
  change Vlasov.IsCoupling (finiteClassPopulationKernel P α β z + finiteClassPopulationKernel Q α β z)
    (κ₀ z) (κ₁ z) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]
    constructor
    · rw [finiteClassPopulationCoupling_fst _ _ _ hW]
      dsimp only [W]
      simp_rw [hrow]
      rw [← finiteClassMarginalKernel_apply asrc hma α z]
      exact finiteClassMarginalKernel_normalized_bins_eq_original_at κ₀ S hS hdS fallbackS z hcoverS
    · rw [finiteClassPopulationCoupling_snd _ _ _ hW]
      dsimp only [W]
      simp_rw [hcol]
      rw [← finiteClassMarginalKernel_apply btgt hmb β z]
      exact finiteClassMarginalKernel_normalized_bins_eq_original_at κ₁ T hT hdT fallbackT z hcoverT
  · rw [hsplit]
    apply finiteClassPopulationCoupling_ae_of_pos
    refine positive_classFlow_bin_legal (W z) (asrc z) (btgt z) hW hrow hcol
      (fun i ↦ α i z) (fun j ↦ β j z) S T ?_ ?_ allowed ?_ hbins
    · intro i hi
      apply normalizedActualBinKernel_supported_of_mass_ne_zero κ₀ (S i) (hS i) (fallbackS i) z
      intro heq
      have he : asrc z i = 0 := by simp only [asrc, measureReal_def, heq, ENNReal.toReal_zero]
      exact (ne_of_gt hi) he
    · intro j hj
      apply normalizedActualBinKernel_supported_of_mass_ne_zero κ₁ (T j) (hT j) (fallbackT j) z
      intro heq
      have he : btgt z j = 0 := by simp only [btgt, measureReal_def, heq, ENNReal.toReal_zero]
      exact (ne_of_gt hj) he
    · intro i j hn
      obtain ⟨hp, hq⟩ := hzero i j hn
      simp only [W, hp, hq, add_zero]
  · rw [finiteClassPopulationKernel_apply _ hmQ, finiteClassPopulationCoupling_mass _ _ _ hQ]
    exact ENNReal.ofReal_le_ofReal hmass

end OTSelector.Reconstruction
