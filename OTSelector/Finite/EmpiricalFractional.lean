import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import OTSelector.Finite.FractionalGauge
import OTSelector.Finite.FractionalOptimal
import OTSelector.Finite.PerturbedValue
import OTSelector.Probability.EmpiricalMeasure
import OTSelector.Transport.Coupling.CostEquivalence

/-!
# Finite.EmpiricalFractional

**Conditions:** Positive sample size, arbitrary sample maps and measurable singletons; the optimal-face equivalence uses nonnegative real costs.

**Objects:** The empirical coupling with atom mass Pij/n and its converse matrix, which divides repeated-atom mass among all representing indices.

**Proof detail:** Compute both marginals using stochastic row/column sums; split coupling atoms by sample multiplicities, recover the original measure, and transport linear cost integrals and optimality in both directions.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22), Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).

Source relation (composition): Discrete Kantorovich couplings and Birkhoff provide the framework. Exact handling of repeated observations by multiplicity splitting, the full two-way representation and its cost normalization are local finite-measure constructions.
-/

/-!
# Fractional matrices and empirical coupling measures

The matrix convention has unit row and column sums. Its empirical measure gives mass
`P i j / n` to the labelled pair `(X i, Y j)`, adding masses when observations repeat.
All constructions use arbitrary sample maps, independently of the height/mark model.
For positive sample size and measurable singletons, every coupling of the empirical marginals
is represented: each pair-atom is divided among all indices producing its two observations.
No injectivity of either sample map is assumed. This representation preserves the full optimal
face for nonnegative real costs and supplies the actual distance-slack affine comparison.
`NeZero n` is the positive-sample-size assumption; no limiting pressure theorem is asserted.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace OTSelector

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {n : ℕ}

/-- The probability-normalized atomic measure associated with a real matrix. -/
noncomputable def fractionalEmpiricalMeasure (X : Fin n → α) (Y : Fin n → β)
    (P : Matrix (Fin n) (Fin n) ℝ) : Measure (α × β) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, ∑ j, ENNReal.ofReal (P i j) • Measure.dirac (X i, Y j)

/-- A doubly-stochastic matrix gives exactly the prescribed empirical marginals. -/
theorem fractionalEmpiricalMeasure_isCoupling (X : Fin n → α) (Y : Fin n → β)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    Vlasov.IsCoupling (fractionalEmpiricalMeasure X Y P)
      (empiricalMeasure X) (empiricalMeasure Y) := by
  have hr (i : Fin n) : ∑ j, ENNReal.ofReal (P i j) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hP.1 i j),
      sum_row_of_mem_doublyStochastic hP, ENNReal.ofReal_one]
  have hc (j : Fin n) : ∑ i, ENNReal.ofReal (P i j) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hP.1 i j),
      sum_col_of_mem_doublyStochastic hP, ENNReal.ofReal_one]
  constructor
  · rw [fractionalEmpiricalMeasure, empiricalMeasure, Measure.map_smul,
      Measure.map_finset_sum' measurable_fst.aemeasurable]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Measure.map_finset_sum' measurable_fst.aemeasurable]
    simp_rw [Measure.map_smul, Measure.map_dirac' measurable_fst]
    simp only [← Finset.sum_smul, hr, one_smul]
  · rw [fractionalEmpiricalMeasure, empiricalMeasure, Measure.map_smul,
      Measure.map_finset_sum' measurable_snd.aemeasurable]
    simp_rw [Measure.map_finset_sum' measurable_snd.aemeasurable,
      Measure.map_smul, Measure.map_dirac' measurable_snd]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hc, one_smul]

/-- For positive sample size the matrix coupling has total mass one. -/
theorem fractionalEmpiricalMeasure_isProbabilityMeasure [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    IsProbabilityMeasure (fractionalEmpiricalMeasure X Y P) := by
  constructor
  have hm := (fractionalEmpiricalMeasure_isCoupling X Y P hP).1
  have hu := congrArg (fun μ : Measure α ↦ μ Set.univ) hm
  simpa [Measure.map_apply measurable_fst MeasurableSet.univ] using hu

/-- The matrix-generated empirical coupling bundled as a probability measure. -/
noncomputable def fractionalEmpiricalCoupling [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n)) : ProbabilityMeasure (α × β) :=
  ⟨fractionalEmpiricalMeasure X Y P,
    fractionalEmpiricalMeasure_isProbabilityMeasure X Y P hP⟩

@[simp]
theorem fractionalEmpiricalCoupling_toMeasure [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    (fractionalEmpiricalCoupling X Y P hP : Measure (α × β)) =
      fractionalEmpiricalMeasure X Y P := rfl

/-- Every strongly measurable real paired function is integrable for the finite matrix measure. -/
theorem integrable_fractionalEmpiricalMeasure [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    {f : α × β → ℝ} (hf : StronglyMeasurable f) :
    Integrable f (fractionalEmpiricalMeasure X Y P) := by
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i _
    apply integrable_finsetSum_measure.mpr
    intro j _
    exact (integrable_dirac' hf (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- The integral is the normalized matrix cost, for any strongly measurable real readout. -/
theorem integral_fractionalEmpiricalMeasure
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n)) {f : α × β → ℝ}
    (hf : StronglyMeasurable f) :
    ∫ z, f z ∂(fractionalEmpiricalMeasure X Y P) =
      fractionalAssignmentCost (fun i j ↦ f (X i, Y j)) P / (n : ℝ) := by
  have hint (i j : Fin n) :
      Integrable f (ENNReal.ofReal (P i j) • Measure.dirac (X i, Y j)) :=
    (integrable_dirac' hf (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [fractionalEmpiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun i _ ↦ integrable_finsetSum_measure.mpr (fun j _ ↦ hint i j))]
  simp_rw [integral_finsetSum_measure (fun j _ ↦ hint _ j), integral_smul_measure,
    integral_dirac' _ _ hf, ENNReal.toReal_ofReal (hP.1 _ _)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    fractionalAssignmentCost, div_eq_mul_inv, mul_comm]


/-- Number of sample indices representing a given observation; repeated points are retained. -/
noncomputable def sampleMultiplicity (X : Fin n → α) (a : α) : ℕ :=
  Nat.card {i // X i = a}

omit [MeasurableSpace α] in
private theorem sampleMultiplicity_eq_card [DecidableEq α] (X : Fin n → α) (a : α) :
    sampleMultiplicity X a = (Finset.univ.filter fun i ↦ X i = a).card := by
  simp [sampleMultiplicity, Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [MeasurableSpace α] in
private theorem sampleMultiplicity_pos (X : Fin n → α) (i : Fin n) :
    0 < sampleMultiplicity X (X i) := by
  classical
  rw [sampleMultiplicity_eq_card]
  exact Finset.card_pos.mpr ⟨i, by simp⟩

omit [MeasurableSpace α] in
private theorem sum_div_sampleMultiplicity [DecidableEq α] (X : Fin n → α) (f : α → ℝ) :
    ∑ i, f (X i) / (sampleMultiplicity X (X i) : ℝ) =
      ∑ x ∈ Finset.univ.image X, f x := by
  classical
  simp_rw [sampleMultiplicity_eq_card]
  rw [← Finset.sum_fiberwise_of_maps_to'
    (s := Finset.univ) (t := Finset.univ.image X)
    (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun x ↦ f x / ((Finset.univ.filter fun k ↦ X k = x).card : ℝ))]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hn : (Finset.univ.filter fun k ↦ X k = X i).card ≠ 0 := by
    apply Finset.card_ne_zero.mpr
    exact ⟨i, by simp⟩
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel₀ _ (by exact_mod_cast hn)

/-- Split each pair-atom uniformly among all of its source and target sample labels. -/
noncomputable def empiricalCouplingMatrix (X : Fin n → α) (Y : Fin n → β)
    (γ : Measure (α × β)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (n : ℝ) * γ.real {(X i, Y j)} /
    ((sampleMultiplicity X (X i) : ℝ) * (sampleMultiplicity Y (Y j) : ℝ))

private theorem fractionalAssignmentCost_empiricalCouplingMatrix [DecidableEq α] [DecidableEq β]
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β)) (f : α × β → ℝ) :
    fractionalAssignmentCost (fun i j ↦ f (X i, Y j)) (empiricalCouplingMatrix X Y γ) =
      (n : ℝ) * ∑ a ∈ Finset.univ.image X, ∑ b ∈ Finset.univ.image Y,
        γ.real {(a, b)} * f (a, b) := by
  classical
  unfold fractionalAssignmentCost empiricalCouplingMatrix
  simp_rw [show ∀ i j, (n : ℝ) * γ.real {(X i, Y j)} /
      ((sampleMultiplicity X (X i) : ℝ) * (sampleMultiplicity Y (Y j) : ℝ)) *
        f (X i, Y j) =
      (n : ℝ) * ((γ.real {(X i, Y j)} * f (X i, Y j)) /
        (sampleMultiplicity Y (Y j) : ℝ)) / (sampleMultiplicity X (X i) : ℝ)
    from fun i j ↦ by ring]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]
  rw [← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ i, (∑ j, (γ.real {(X i, Y j)} * f (X i, Y j)) /
        (sampleMultiplicity Y (Y j) : ℝ)) / (sampleMultiplicity X (X i) : ℝ) := by
      simp only [mul_div_assoc]
    _ = _ := by
      have hy (i : Fin n) := sum_div_sampleMultiplicity Y
        (fun b ↦ γ.real {(X i, b)} * f (X i, b))
      simp_rw [hy]
      exact sum_div_sampleMultiplicity X
        (fun a ↦ ∑ b ∈ Finset.univ.image Y, γ.real {(a, b)} * f (a, b))

private theorem integral_eq_sum_pair_atoms
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (γ : Measure (α × β)) [IsFiniteMeasure γ]
    (S : Finset α) (T : Finset β)
    (hsupport : ∀ᵐ z ∂γ, z ∈ S.product T)
    {f : α × β → ℝ} (hf : StronglyMeasurable f) :
    ∫ z, f z ∂γ = ∑ a ∈ S, ∑ b ∈ T, γ.real {(a, b)} * f (a, b) := by
  classical
  have hd := Measure.ae_mem_finset_iff.mp hsupport
  conv_lhs => rw [hd]
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac' _ _ hf, smul_eq_mul,
      ← measureReal_def]
    exact Finset.sum_product S T _
  · intro z _
    exact (integrable_dirac' hf (by simp)).smul_measure (measure_ne_top _ _)

section AtomicAux

private theorem ae_mem_prod_of_marginal_support {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DecidableEq α] [DecidableEq β]
    (γ : Measure (α × β)) (S : Finset α) (T : Finset β)
    (hS : ∀ᵐ x ∂γ.map Prod.fst, x ∈ S)
    (hT : ∀ᵐ y ∂γ.map Prod.snd, y ∈ T) :
    ∀ᵐ z ∂γ, z ∈ S.product T := by
  have hfst := (ae_map_iff measurable_fst.aemeasurable
    S.finite_toSet.measurableSet).mp hS
  have hsnd := (ae_map_iff measurable_snd.aemeasurable
    T.finite_toSet.measurableSet).mp hT
  filter_upwards [hfst, hsnd] with z hzS hzT
  exact Finset.mem_product.mpr ⟨hzS, hzT⟩

private theorem sum_atoms_right {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DecidableEq α] [DecidableEq β]
    (γ : Measure (α × β)) [IsFiniteMeasure γ] (T : Finset β)
    (hT : ∀ᵐ z ∂γ, z.2 ∈ T) (x : α) :
    ∑ y ∈ T, γ.real {(x, y)} = (γ.map Prod.fst).real {x} := by
  calc
    _ = ∑ z ∈ T.image (fun y => (x, y)), γ.real {z} := by
      rw [Finset.sum_image]
      intro y hy z hz h
      exact congrArg Prod.snd h
    _ = γ.real (T.image fun y => (x, y)) := sum_measureReal_singleton _
    _ = γ.real (Prod.fst ⁻¹' {x}) := by
      apply measureReal_congr
      filter_upwards [hT] with z hz
      rcases z with ⟨a, b⟩
      apply propext
      change ((a, b) ∈ T.image (fun y => (x, y))) ↔ a = x
      simp only [Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact hxy.1.symm
      · intro h
        exact ⟨b, hz, h.symm, rfl⟩
    _ = _ := (map_measureReal_apply measurable_fst (measurableSet_singleton x)).symm

private theorem empirical_singleton_real {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [DecidableEq α] {n : ℕ}
    (X : Fin n → α) (x : α) :
    (OTSelector.empiricalMeasure X).real {x} =
      ((Finset.univ.filter fun i => X i = x).card : ℝ) / n := by
  simp [OTSelector.empiricalMeasure, measureReal_def, Measure.finsetSum_apply,
    Measure.dirac_apply', Pi.single_apply, Finset.sum_boole, div_eq_mul_inv, mul_comm, eq_comm]

private theorem ae_empirical_mem_image {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [DecidableEq α] {n : ℕ}
    (X : Fin n → α) :
    ∀ᵐ x ∂OTSelector.empiricalMeasure X, x ∈ Finset.univ.image X := by
  simp [ae_iff, OTSelector.empiricalMeasure, Measure.finsetSum_apply]

private theorem sum_atoms_left {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DecidableEq α] [DecidableEq β]
    (γ : Measure (α × β)) [IsFiniteMeasure γ] (S : Finset α)
    (hS : ∀ᵐ z ∂γ, z.1 ∈ S) (y : β) :
    ∑ x ∈ S, γ.real {(x, y)} = (γ.map Prod.snd).real {y} := by
  calc
    _ = ∑ z ∈ S.image (fun x => (x, y)), γ.real {z} := by
      rw [Finset.sum_image]
      intro x hx z hz h
      exact congrArg Prod.fst h
    _ = γ.real (S.image fun x => (x, y)) := sum_measureReal_singleton _
    _ = γ.real (Prod.snd ⁻¹' {y}) := by
      apply measureReal_congr
      filter_upwards [hS] with z hz
      rcases z with ⟨a, b⟩
      apply propext
      change ((a, b) ∈ S.image (fun x => (x, y))) ↔ b = y
      simp only [Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact hxy.2.symm
      · intro h
        exact ⟨a, hz, rfl, h.symm⟩
    _ = _ := (map_measureReal_apply measurable_snd (measurableSet_singleton y)).symm

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [DecidableEq α] [DecidableEq β] {n : ℕ}

private theorem empirical_coupling_ae_support
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β))
    (hγ : Vlasov.IsCoupling γ (OTSelector.empiricalMeasure X) (OTSelector.empiricalMeasure Y)) :
    ∀ᵐ z ∂γ, z ∈ (Finset.univ.image X).product (Finset.univ.image Y) := by
  apply ae_mem_prod_of_marginal_support
  · rw [hγ.1]
    exact ae_empirical_mem_image X
  · rw [hγ.2]
    exact ae_empirical_mem_image Y

private theorem empirical_coupling_atomic
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β))
    (hγ : Vlasov.IsCoupling γ (OTSelector.empiricalMeasure X) (OTSelector.empiricalMeasure Y)) :
    γ = ∑ z ∈ (Finset.univ.image X).product (Finset.univ.image Y),
      γ {z} • Measure.dirac z :=
  Measure.ae_mem_finset_iff.mp (empirical_coupling_ae_support X Y γ hγ)

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [DecidableEq α] [DecidableEq β] in
private theorem empirical_coupling_isProbabilityMeasure [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β))
    (hγ : Vlasov.IsCoupling γ (OTSelector.empiricalMeasure X) (OTSelector.empiricalMeasure Y)) :
    IsProbabilityMeasure γ := by
  constructor
  simpa [Measure.map_apply measurable_fst MeasurableSet.univ] using
    congrArg (fun μ : Measure α => μ Set.univ) hγ.1

private theorem empirical_coupling_sum_atoms_right [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β))
    (hγ : Vlasov.IsCoupling γ (OTSelector.empiricalMeasure X) (OTSelector.empiricalMeasure Y))
    (x : α) :
    ∑ y ∈ Finset.univ.image Y, γ.real {(x, y)} = (OTSelector.empiricalMeasure X).real {x} := by
  let := empirical_coupling_isProbabilityMeasure X Y γ hγ
  have hT : ∀ᵐ z ∂γ, z.2 ∈ Finset.univ.image Y :=
    (empirical_coupling_ae_support X Y γ hγ).mono fun z hz => (Finset.mem_product.mp hz).2
  simpa [hγ.1] using sum_atoms_right γ (Finset.univ.image Y) hT x

private theorem empirical_coupling_sum_atoms_left [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β))
    (hγ : Vlasov.IsCoupling γ (OTSelector.empiricalMeasure X) (OTSelector.empiricalMeasure Y))
    (y : β) :
    ∑ x ∈ Finset.univ.image X, γ.real {(x, y)} = (OTSelector.empiricalMeasure Y).real {y} := by
  let := empirical_coupling_isProbabilityMeasure X Y γ hγ
  have hS : ∀ᵐ z ∂γ, z.1 ∈ Finset.univ.image X :=
    (empirical_coupling_ae_support X Y γ hγ).mono fun z hz => (Finset.mem_product.mp hz).1
  simpa [hγ.2] using sum_atoms_left γ (Finset.univ.image X) hS y


end AtomicAux


/-- Every empirical coupling splits into a doubly-stochastic matrix, even with repeated samples. -/
theorem empiricalCouplingMatrix_mem_doublyStochastic
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β))
    (hγ : Vlasov.IsCoupling γ (empiricalMeasure X) (empiricalMeasure Y)) :
    empiricalCouplingMatrix X Y γ ∈ doublyStochastic ℝ (Fin n) := by
  classical
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hX (i : Fin n) : (sampleMultiplicity X (X i) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (sampleMultiplicity_pos X i).ne'
  have hY (j : Fin n) : (sampleMultiplicity Y (Y j) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (sampleMultiplicity_pos Y j).ne'
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_, fun j ↦ ?_⟩
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · simp only [empiricalCouplingMatrix]
    simp_rw [show ∀ j, (n : ℝ) * γ.real {(X i, Y j)} /
        ((sampleMultiplicity X (X i) : ℝ) * (sampleMultiplicity Y (Y j) : ℝ)) =
        ((n : ℝ) / (sampleMultiplicity X (X i) : ℝ)) *
          (γ.real {(X i, Y j)} / (sampleMultiplicity Y (Y j) : ℝ)) from fun j ↦ by ring]
    rw [← Finset.mul_sum, sum_div_sampleMultiplicity Y (fun b ↦ γ.real {(X i, b)}),
      empirical_coupling_sum_atoms_right X Y γ hγ, empirical_singleton_real,
      ← sampleMultiplicity_eq_card X (X i)]
    field_simp [hX i]
  · simp only [empiricalCouplingMatrix]
    simp_rw [show ∀ i, (n : ℝ) * γ.real {(X i, Y j)} /
        ((sampleMultiplicity X (X i) : ℝ) * (sampleMultiplicity Y (Y j) : ℝ)) =
        ((n : ℝ) / (sampleMultiplicity Y (Y j) : ℝ)) *
          (γ.real {(X i, Y j)} / (sampleMultiplicity X (X i) : ℝ)) from fun i ↦ by ring]
    rw [← Finset.mul_sum, sum_div_sampleMultiplicity X (fun a ↦ γ.real {(a, Y j)}),
      empirical_coupling_sum_atoms_left X Y γ hγ, empirical_singleton_real,
      ← sampleMultiplicity_eq_card Y (Y j)]
    field_simp [hY j]

/-- Splitting repeated atoms preserves every strongly measurable real paired cost exactly. -/
theorem fractionalAssignmentCost_empiricalCouplingMatrix_div
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β))
    (hγ : Vlasov.IsCoupling γ (empiricalMeasure X) (empiricalMeasure Y))
    {f : α × β → ℝ} (hf : StronglyMeasurable f) :
    fractionalAssignmentCost (fun i j ↦ f (X i, Y j)) (empiricalCouplingMatrix X Y γ) /
      (n : ℝ) = ∫ z, f z ∂γ := by
  classical
  have := empirical_coupling_isProbabilityMeasure X Y γ hγ
  rw [fractionalAssignmentCost_empiricalCouplingMatrix,
    ← integral_eq_sum_pair_atoms γ _ _ (empirical_coupling_ae_support X Y γ hγ) hf]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- Recombining the uniformly split matrix recovers the entire original empirical coupling. -/
theorem fractionalEmpiricalMeasure_empiricalCouplingMatrix
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β))
    (hγ : Vlasov.IsCoupling γ (empiricalMeasure X) (empiricalMeasure Y)) :
    fractionalEmpiricalMeasure X Y (empiricalCouplingMatrix X Y γ) = γ := by
  have := empirical_coupling_isProbabilityMeasure X Y γ hγ
  have hP := empiricalCouplingMatrix_mem_doublyStochastic X Y γ hγ
  have := fractionalEmpiricalMeasure_isProbabilityMeasure X Y _ hP
  have hint (f : α × β → ℝ) (hf : StronglyMeasurable f) :
      ∫ z, f z ∂(fractionalEmpiricalMeasure X Y (empiricalCouplingMatrix X Y γ)) =
        ∫ z, f z ∂γ := by
    rw [integral_fractionalEmpiricalMeasure X Y _ hP hf]
    exact fractionalAssignmentCost_empiricalCouplingMatrix_div X Y γ hγ hf
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (fractionalEmpiricalMeasure X Y (empiricalCouplingMatrix X Y γ)).real s = γ.real s
  simpa only [integral_indicator_one hs] using
    hint (s.indicator 1) (stronglyMeasurable_const.indicator hs)

/-- The matrix model represents every coupling of the empirical marginals, with no distinctness
assumption on either sample. -/
theorem isCoupling_empirical_iff_exists_doublyStochastic
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (γ : Measure (α × β)) :
    Vlasov.IsCoupling γ (empiricalMeasure X) (empiricalMeasure Y) ↔
      ∃ P ∈ doublyStochastic ℝ (Fin n), fractionalEmpiricalMeasure X Y P = γ := by
  constructor
  · intro hγ
    exact ⟨empiricalCouplingMatrix X Y γ,
      empiricalCouplingMatrix_mem_doublyStochastic X Y γ hγ,
      fractionalEmpiricalMeasure_empiricalCouplingMatrix X Y γ hγ⟩
  · rintro ⟨P, hP, rfl⟩
    exact fractionalEmpiricalMeasure_isCoupling X Y P hP


/-- On spaces with measurable singletons, every finite-valued real paired function is integrable
on the empirical matrix measure, without global measurability or boundedness assumptions. -/
theorem integrable_fractionalEmpiricalMeasure_of_singletons
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    (f : α × β → ℝ) : Integrable f (fractionalEmpiricalMeasure X Y P) := by
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i _
    apply integrable_finsetSum_measure.mpr
    intro j _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- Exact finite paired readout for arbitrary real functions on measurable-singleton spaces. -/
theorem integral_fractionalEmpiricalMeasure_of_singletons
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n)) (f : α × β → ℝ) :
    ∫ z, f z ∂(fractionalEmpiricalMeasure X Y P) =
      fractionalAssignmentCost (fun i j ↦ f (X i, Y j)) P / (n : ℝ) := by
  have hint (i j : Fin n) :
      Integrable f (ENNReal.ofReal (P i j) • Measure.dirac (X i, Y j)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [fractionalEmpiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun i _ ↦ integrable_finsetSum_measure.mpr (fun j _ ↦ hint i j))]
  simp_rw [integral_finsetSum_measure (fun j _ ↦ hint _ j), integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal (hP.1 _ _)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    fractionalAssignmentCost, div_eq_mul_inv, mul_comm]

/-- Nonnegative finite costs agree with the existing extended-valued coupling-cost API. -/
theorem couplingCost_fractionalEmpiricalMeasure
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n))
    (cost : α → β → ℝ) (hcost : ∀ a b, 0 ≤ cost a b) :
    couplingCost (fun a b ↦ ENNReal.ofReal (cost a b)) (fractionalEmpiricalMeasure X Y P) =
      ENNReal.ofReal (fractionalAssignmentCost (fun i j ↦ cost (X i) (Y j)) P / (n : ℝ)) := by
  rw [couplingCost, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_fractionalEmpiricalMeasure_of_singletons X Y P (fun z ↦ cost z.1 z.2))
    (Filter.Eventually.of_forall fun z ↦ hcost z.1 z.2),
    integral_fractionalEmpiricalMeasure_of_singletons X Y P hP]

/-- Matrix optimality is exactly optimality among all empirical coupling measures. -/
theorem optimalFractionalAssignment_iff_isOptimalCoupling
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P ∈ doublyStochastic ℝ (Fin n))
    (cost : α → β → ℝ) (hcost : ∀ a b, 0 ≤ cost a b) :
    OptimalFractionalAssignment (fun i j ↦ cost (X i) (Y j)) P ↔
      IsOptimalCoupling (fun a b ↦ ENNReal.ofReal (cost a b))
        (empiricalMeasure X) (empiricalMeasure Y) (fractionalEmpiricalMeasure X Y P) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  constructor
  · intro hopt
    refine ⟨fractionalEmpiricalMeasure_isCoupling X Y P hP, fun γ hγ ↦ ?_⟩
    obtain ⟨Q, hQ, rfl⟩ := (isCoupling_empirical_iff_exists_doublyStochastic X Y γ).mp hγ
    rw [couplingCost_fractionalEmpiricalMeasure X Y P hP cost hcost,
      couplingCost_fractionalEmpiricalMeasure X Y Q hQ cost hcost]
    exact ENNReal.ofReal_le_ofReal ((div_le_div_iff_of_pos_right hn).mpr (hopt.2 Q hQ))
  · intro hopt
    refine ⟨hP, fun Q hQ ↦ ?_⟩
    have h := hopt.2 _ (fractionalEmpiricalMeasure_isCoupling X Y Q hQ)
    rw [couplingCost_fractionalEmpiricalMeasure X Y P hP cost hcost,
      couplingCost_fractionalEmpiricalMeasure X Y Q hQ cost hcost] at h
    have hQcost : 0 ≤ fractionalAssignmentCost (fun i j ↦ cost (X i) (Y j)) Q :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ mul_nonneg (hQ.1 i j) (hcost _ _)
    exact (div_le_div_iff_of_pos_right hn).mp
      ((ENNReal.ofReal_le_ofReal_iff (div_nonneg hQcost hn.le)).mp h)

/-- Every optimal empirical coupling has an optimal matrix representative, including all repeats. -/
theorem isOptimalCoupling_empirical_iff_exists_optimalFractional
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [NeZero n]
    (X : Fin n → α) (Y : Fin n → β) (cost : α → β → ℝ)
    (hcost : ∀ a b, 0 ≤ cost a b) (γ : Measure (α × β)) :
    IsOptimalCoupling (fun a b ↦ ENNReal.ofReal (cost a b))
        (empiricalMeasure X) (empiricalMeasure Y) γ ↔
      ∃ P, OptimalFractionalAssignment (fun i j ↦ cost (X i) (Y j)) P ∧
        fractionalEmpiricalMeasure X Y P = γ := by
  constructor
  · intro hγ
    obtain ⟨P, hP, rfl⟩ := (isCoupling_empirical_iff_exists_doublyStochastic X Y γ).mp hγ.1
    exact ⟨P, (optimalFractionalAssignment_iff_isOptimalCoupling X Y P hP cost hcost).mpr hγ,
      rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact (optimalFractionalAssignment_iff_isOptimalCoupling X Y P hP.1 cost hcost).mp hP

/-- The actual distance-slack pressure has the affine comparison against every original empirical
optimal coupling. Its readout is the integral on the physical pair space. -/
theorem perturbedDistanceSlackValue_div_le_of_empirical_optimal
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M] [PseudoMetricSpace M]
    [NeZero n] (X Y : Fin n → M) (φ : M → ℝ) (probe : M × M → ℝ)
    (k : ℝ) (hk : 0 < k) (t : ℝ) (γ : Measure (M × M))
    (hγ : IsOptimalCoupling edist (empiricalMeasure X) (empiricalMeasure Y) γ) :
    perturbedAssignmentValue (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
        (fun i j ↦ probe (X i, Y j)) t / (n : ℝ) ≤
      perturbedAssignmentValue (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
        (fun i j ↦ probe (X i, Y j)) 0 / (n : ℝ) + t * ∫ z, probe z ∂γ := by
  have hdist : (edist : M → M → ℝ≥0∞) = fun x y ↦ ENNReal.ofReal (dist x y) :=
    funext fun x ↦ funext fun y ↦ edist_dist x y
  rw [hdist] at hγ
  obtain ⟨P, hP, rfl⟩ :=
    (isOptimalCoupling_empirical_iff_exists_optimalFractional X Y dist
      (fun _ _ ↦ dist_nonneg) γ).mp hγ
  rw [integral_fractionalEmpiricalMeasure_of_singletons X Y P hP.1 probe]
  exact perturbedDistanceSlackValue_div_le_of_optimalFractional
    (Nat.pos_of_ne_zero (NeZero.ne n)) X Y φ _ P k hk t hP

end OTSelector
