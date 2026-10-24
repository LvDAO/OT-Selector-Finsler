import OTSelector.Reconstruction.PopulationUniformEnergyBound
import OTSelector.Probability.CavitySemidiscretePressurePhysical
import OTSelector.Probability.CavitySemidiscreteTiltConcavity
import OTSelector.Probability.CavitySemidiscretePressureRegularity
import OTSelector.Probability.CavitySemidiscreteJointReadout
import OTSelector.Probability.CavitySemidiscretePressureJoint

/-!
# The Dirichlet tilted allocation energy under the original uniform bound

The exact semidiscrete mean identity transfers the uniform physical empirical
energy bound to the same original Dirichlet environment.  The transfer uses the
zero-tilt identity only: a tilted optimum pays at most twice the bounded probe
correction in base energy over the zero-tilt semidiscrete value, and the latter
has exactly the original zero-tilt empirical pressure as its expectation.

No differentiability, limiting pressure, geometric coercivity or selected
measurable optimizer is assumed.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] {m : ℕ}

/-! ## Pure semidiscrete comparison -/

/-- A tilted semidiscrete objective splits into the base objective and the tilt. -/
theorem semidiscreteAllocationCost_add_tilt
    (μ : Measure S) (c g : S → Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ) (t : ℝ) :
    semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) a =
      semidiscreteAllocationCost μ c a + t * semidiscreteAllocationCost μ g a :=
  OTSelector.Probability.semidiscreteAllocationCost_tilt_affine μ c g a ha hc hg t

/-- A feasible allocation has bounded probe objective whenever the probe is bounded. -/
theorem abs_semidiscreteAllocationCost_le_of_bounded
    (μ : Measure S) [IsProbabilityMeasure μ]
    (g : S → Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    {G : ℝ} (hG : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G) :
    |semidiscreteAllocationCost μ g a| ≤ G := by
  have hsum : Integrable (fun s ↦ ∑ j, a s j * g s j) μ :=
    integrable_finsetSum Finset.univ (fun j _ ↦ ha.integrable_mul g hg j)
  calc
    |semidiscreteAllocationCost μ g a| ≤ ∫ s, ‖∑ j, a s j * g s j‖ ∂μ := by
      rw [semidiscreteAllocationCost, ← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ _s, G ∂μ := by
      apply integral_mono_ae hsum.norm (integrable_const G)
      filter_upwards [ha.nonneg, ha.sum_one, hG] with s hn hs hg
      calc
        ‖∑ j, a s j * g s j‖ ≤ ∑ j, ‖a s j * g s j‖ := norm_sum_le _ _
        _ = ∑ j, a s j * |g s j| := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn j)]
        _ ≤ ∑ j, a s j * G :=
          Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hg j) (hn j)
        _ = G := by rw [← Finset.sum_mul, hs, one_mul]
    _ = G := by simp

/-- A tilted optimum pays at most twice the bounded probe correction in base energy
over the zero-tilt semidiscrete value. -/
theorem semidiscreteAllocationCost_le_value_add_two_abs_mul
    (μ : Measure S) [IsProbabilityMeasure μ]
    {p : Fin (m + 1) → ℝ} (hp : p ∈ stdSimplex ℝ (Fin (m + 1)))
    (c g : S → Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    {G : ℝ} (hG : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G) (t : ℝ)
    (hopt : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) a ≤
        semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) b) :
    semidiscreteAllocationCost μ c a ≤ semidiscreteValue μ c p + 2 * |t| * G := by
  have hct : ∀ j, Integrable (fun s ↦ c s j + t * g s j) μ :=
    fun j ↦ (hc j).add ((hg j).const_mul t)
  have hval : semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p =
      semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) a :=
    semidiscreteValue_eq_cost_of_optimal μ _ hct p a ha hopt
  have hlip : |semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p -
      semidiscreteValue μ c p| ≤ |t| * G := by
    apply semidiscreteValue_abs_sub_le μ _ _ hct hc p hp (|t| * G)
    filter_upwards [hG] with s hs
    intro j
    calc
      |(c s j + t * g s j) - c s j| = |t| * |g s j| := by
        rw [add_sub_cancel_left, abs_mul]
      _ ≤ |t| * G := mul_le_mul_of_nonneg_left (hs j) (abs_nonneg t)
  have hprobe : |semidiscreteAllocationCost μ g a| ≤ G :=
    abs_semidiscreteAllocationCost_le_of_bounded μ g a ha hg hG
  have hsplit := semidiscreteAllocationCost_add_tilt μ c g a ha hc hg t
  have hvalle : semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p ≤
      semidiscreteValue μ c p + |t| * G := by
    have := (abs_le.mp hlip).2
    linarith
  have htprobe : -(t * semidiscreteAllocationCost μ g a) ≤ |t| * G := by
    have habs : |t * semidiscreteAllocationCost μ g a| ≤ |t| * G := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hprobe (abs_nonneg t)
    have := (abs_le.mp habs).1
    linarith
  linarith [hsplit, hval, hvalle, htprobe]

/-! ## Measurable scaling of atomless image laws -/

/-- Multiplication by a nonzero scalar preserves atomlessness of a real image law. -/
theorem nullSingletonClass_map_mul {μ : Measure S} {f : S → ℝ} (hf : Measurable f)
    (h : NullSingletonClass (μ.map f)) {k : ℝ} (hk : k ≠ 0) :
    NullSingletonClass (μ.map (fun s ↦ k * f s)) := by
  constructor
  intro a
  have hpre : (fun z : ℝ ↦ k * z) ⁻¹' {a} = {a / k} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hz
      field_simp at hz ⊢
      linarith
    · intro hz
      rw [hz]
      field_simp
  rw [show (fun s ↦ k * f s) = (fun z : ℝ ↦ k * z) ∘ f from rfl]
  rw [← Measure.map_map (measurable_const_mul k) hf]
  rw [Measure.map_apply (measurable_const_mul k) (measurableSet_singleton a), hpre]
  exact h.measure_singleton (a / k)

/-! ## The Dirichlet tilted allocation energy -/

/-- The original uniform empirical energy bound transfers to the same Dirichlet
environment and every measurable tilted semidiscrete optimum. -/
theorem integral_bipartite_dirichlet_tilted_allocation_energy_le
    {μ : Measure S} [IsProbabilityMeasure μ]
    {ν : Measure T} [IsProbabilityMeasure ν] [NullSingletonClass ν]
    [StandardBorelSpace S] [StandardBorelSpace T] [MeasurableEq T]
    {q : ℕ} {cost : S → T → ℝ} {C : ℝ}
    (hEnergy : PopulationUniformEnergyBound μ ν q cost C)
    (hcostm : Measurable (Function.uncurry cost))
    (hcost : Integrable (Function.uncurry cost) (μ.prod ν))
    (hhat : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ cost x y - cost x z)))
    {probe : S → T → ℝ} (hprobem : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobe : ∀ x y, |probe x y| ≤ G) (t : ℝ)
    (A : (Fin (m + 1) → T) → (Fin (m + 1) → ℝ) →
      S → Fin (m + 1) → ℝ)
    (hA : ∀ j, Measurable (fun z : ((Fin (m + 1) → T) ×
      (Fin (m + 1) → ℝ)) × S ↦ A z.1.1 z.1.2 z.2 j))
    (halloc : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod
      (dirichletOne m)), IsSemidiscreteAllocation μ z.2 (A z.1 z.2))
    (hopt : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod
      (dirichletOne m)), ∀ b, IsSemidiscreteAllocation μ z.2 b →
        semidiscreteAllocationCost μ
          (fun s j ↦ ((m + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)) * cost s (z.1 j) +
            t * probe s (z.1 j)) (A z.1 z.2) ≤
        semidiscreteAllocationCost μ
          (fun s j ↦ ((m + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)) * cost s (z.1 j) +
            t * probe s (z.1 j)) b) :
    Integrable (fun z ↦ semidiscreteAllocationCost μ
      (fun s j ↦ ((m + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)) * cost s (z.1 j))
      (A z.1 z.2)) ((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)) ∧
    (∫ z, semidiscreteAllocationCost μ
      (fun s j ↦ ((m + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)) * cost s (z.1 j))
      (A z.1 z.2) ∂((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m))) ≤
      C + 2 * |t| * (G : ℝ) := by
  let ρ : Measure (Fin (m + 1) → T) := Measure.pi (fun _ : Fin (m + 1) ↦ ν)
  let P : Measure ((Fin (m + 1) → T) × (Fin (m + 1) → ℝ)) :=
    ρ.prod (dirichletOne m)
  let k : ℝ := ((m + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))
  have hk : 0 < k := Real.rpow_pos_of_pos (by positivity) _
  have hkne : k ≠ 0 := hk.ne'
  let base : (Fin (m + 1) → T) → S → Fin (m + 1) → ℝ :=
    fun y s j ↦ k * cost s (y j)
  have hpair (j : Fin (m + 1)) :
      MeasurePreserving (fun z : (Fin (m + 1) → T) × S ↦ (z.2, z.1 j))
        (ρ.prod μ) (μ.prod ν) :=
    Measure.measurePreserving_swap.comp
      ((measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).prod
        (MeasurePreserving.id μ))
  have hcij (j : Fin (m + 1)) :
      Integrable (fun z : (Fin (m + 1) → T) × S ↦ k * cost z.2 (z.1 j))
        (ρ.prod μ) :=
    ((hpair j).integrable_comp_of_integrable hcost).const_mul k
  have hmeasc (j : Fin (m + 1)) :
      Measurable (fun z : (Fin (m + 1) → T) × S ↦ k * cost z.2 (z.1 j)) :=
    (hcostm.comp (measurable_snd.prodMk
      ((measurable_pi_apply j).comp measurable_fst))).const_mul k
  have hcz : ∀ᵐ z ∂P, ∀ j, Integrable (fun s ↦ base z.1 s j) μ :=
    measurePreserving_fst.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j ↦ (hcij j).prod_right_ae))
  have hger : ∀ᵐ z ∂P, ∀ j, Integrable (fun s ↦ probe s (z.1 j)) μ := by
    apply Eventually.of_forall
    intro z j
    apply (integrable_const (G : ℝ)).mono'
      (hprobem.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact Eventually.of_forall fun s ↦ by
      simpa only [Function.uncurry, Function.comp_apply, id_eq, Real.norm_eq_abs]
        using hprobe s (z.1 j)
  have hp : ∀ᵐ z ∂P, z.2 ∈ stdSimplex ℝ (Fin (m + 1)) :=
    measurePreserving_snd.quasiMeasurePreserving.ae (ae_mem_stdSimplex_dirichletOne m)
  have hineq : ∀ᵐ z ∂P, semidiscreteAllocationCost μ (base z.1) (A z.1 z.2) ≤
      semidiscreteValue μ (base z.1) z.2 + 2 * |t| * (G : ℝ) := by
    filter_upwards [halloc, hopt, hp, hcz, hger] with z hz hzopt hzp hzint hgint
    exact semidiscreteAllocationCost_le_value_add_two_abs_mul μ hzp (base z.1)
      (fun s j ↦ probe s (z.1 j)) (A z.1 z.2) hz hzint hgint
      (Eventually.of_forall fun s ↦ fun j ↦ hprobe s (z.1 j)) t
      (by simpa only [base] using hzopt)
  let A' : ((Fin (m + 1) → T) × (Fin (m + 1) → ℝ)) × S →
      Fin (m + 1) → ℝ := fun z ↦ A z.1.1 z.1.2 z.2
  have hbase_int : Integrable (fun z : (Fin (m + 1) → T) ×
      (Fin (m + 1) → ℝ) ↦ semidiscreteAllocationCost μ (base z.1) (A z.1 z.2)) P := by
    simpa only [P, base, A'] using
      integrable_parameterized_dirichlet_allocationCost (m := m) (S := S)
        (V := Fin (m + 1) → T) μ ρ (fun y j s ↦ k * cost s (y j))
        (fun j ↦ hmeasc j) hcij A' (fun j ↦ hA j)
        (by simpa only [A'] using halloc)
  have hhat' : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ k * cost x y - k * cost x z)) := by
    intro y z hyz
    have hm1 : Measurable (fun x : S ↦ cost x y) :=
      hcostm.comp (measurable_id.prodMk measurable_const)
    have hm2 : Measurable (fun x : S ↦ cost x z) :=
      hcostm.comp (measurable_id.prodMk measurable_const)
    have heq : (fun x : S ↦ k * cost x y - k * cost x z) =
        (fun x : S ↦ k * (cost x y - cost x z)) := by
      funext x
      ring
    rw [heq]
    exact nullSingletonClass_map_mul (hm1.sub hm2) (hhat y z hyz) hkne
  have hat : ∀ᵐ y ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ k * cost s (y j) - k * cost s (y l))) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν]
      with y hy
    exact fun j l hjl ↦ hhat' (y j) (y l) (hy.ne hjl)
  have hsd_int : Integrable (fun z : (Fin (m + 1) → T) ×
      (Fin (m + 1) → ℝ) ↦ semidiscreteValue μ (base z.1) z.2) P := by
    simpa only [P, base] using
      integrable_parameterized_dirichlet_semidiscreteValue (m := m) (S := S)
        (V := Fin (m + 1) → T) μ ρ (fun y j s ↦ k * cost s (y j))
        (fun j ↦ hmeasc j) hcij hat
  have hmean := integral_bipartite_pressure_eq_dirichlet_semidiscreteValue
    (m := m) μ ν (fun x y ↦ k * cost x y) (fun _ _ ↦ (0 : ℝ))
    (hcostm.const_mul k) (hcost.const_mul k) measurable_const hhat' 0 (by simp) 0
  let f : (Fin (m + 1) → S) × (Fin (m + 1) → T) → ℝ := fun ξ ↦
    perturbedAssignmentValue (fun i j ↦ k * cost (ξ.1 i) (ξ.2 j))
      (fun _ _ ↦ (0 : ℝ)) 0 / (m + 1 : ℕ)
  have hD_le : (∫ y, ∫ p, semidiscreteValue μ (fun s j ↦ k * cost s (y j)) p
      ∂dirichletOne m ∂ρ) ≤ C := by
    calc
      (∫ y, ∫ p, semidiscreteValue μ (fun s j ↦ k * cost s (y j)) p
          ∂dirichletOne m ∂ρ)
          = ∫ q : (Fin (m + 1) → T) × (Fin (m + 1) → S),
              perturbedAssignmentValue (fun i j ↦ k * cost (q.2 i) (q.1 j))
                (fun _ _ ↦ (0 : ℝ)) 0 / (m + 1 : ℕ)
                ∂(ρ.prod (Measure.pi (fun _ : Fin (m + 1) ↦ μ))) := by
            simpa only [ρ, zero_mul, add_zero] using hmean.2.symm
      _ = ∫ ξ : (Fin (m + 1) → S) × (Fin (m + 1) → T), f ξ
            ∂((Measure.pi (fun _ : Fin (m + 1) ↦ μ)).prod
              (Measure.pi (fun _ : Fin (m + 1) ↦ ν))) :=
          integral_prod_swap f
      _ ≤ C := by
          have hzero := (hEnergy (m + 1) (Nat.succ_pos m)).1.2
          dsimp only at hzero
          have hf_eq : (∫ ξ : (Fin (m + 1) → S) × (Fin (m + 1) → T), f ξ
                ∂((Measure.pi (fun _ : Fin (m + 1) ↦ μ)).prod
                  (Measure.pi (fun _ : Fin (m + 1) ↦ ν)))) =
              ∫ ξ : (Fin (m + 1) → S) × (Fin (m + 1) → T),
                perturbedAssignmentValue (fun i j ↦ k * cost (ξ.1 i) (ξ.2 j))
                  0 0 / (m + 1 : ℕ)
                ∂((Measure.pi (fun _ : Fin (m + 1) ↦ μ)).prod
                  (Measure.pi (fun _ : Fin (m + 1) ↦ ν))) := by
            apply integral_congr_ae
            filter_upwards with ξ
            simp only [f, k, perturbedAssignmentValue, perturbedEdgeCost_zero]
          rw [hf_eq]
          exact hzero
  have hmono : (∫ z, semidiscreteAllocationCost μ (base z.1) (A z.1 z.2) ∂P) ≤
      (∫ z, semidiscreteValue μ (base z.1) z.2 ∂P) + 2 * |t| * (G : ℝ) := by
    have hconst : Integrable
        (fun _z : (Fin (m + 1) → T) × (Fin (m + 1) → ℝ) ↦
          2 * |t| * (G : ℝ)) P := integrable_const _
    have hle := integral_mono_ae hbase_int (hsd_int.add hconst) hineq
    calc
      (∫ z, semidiscreteAllocationCost μ (base z.1) (A z.1 z.2) ∂P)
          ≤ ∫ z, (semidiscreteValue μ (base z.1) z.2 + 2 * |t| * (G : ℝ)) ∂P := hle
      _ = (∫ z, semidiscreteValue μ (base z.1) z.2 ∂P) + 2 * |t| * (G : ℝ) := by
          rw [integral_add hsd_int hconst]
          simp
  have hsd_le : (∫ z, semidiscreteValue μ (base z.1) z.2 ∂P) ≤ C := by
    calc
      (∫ z, semidiscreteValue μ (base z.1) z.2 ∂P)
          = ∫ y, ∫ p, semidiscreteValue μ (base y) p
              ∂dirichletOne m ∂ρ := integral_prod _ hsd_int
      _ = ∫ y, ∫ p, semidiscreteValue μ (fun s j ↦ k * cost s (y j)) p
              ∂dirichletOne m ∂ρ := rfl
      _ ≤ C := hD_le
  refine ⟨hbase_int, ?_⟩
  calc
    (∫ z, semidiscreteAllocationCost μ (base z.1) (A z.1 z.2) ∂P)
        ≤ (∫ z, semidiscreteValue μ (base z.1) z.2 ∂P) + 2 * |t| * (G : ℝ) := hmono
    _ ≤ C + 2 * |t| * (G : ℝ) := add_le_add hsd_le le_rfl

/-- The same uniform empirical energy bound controls the Dirichlet semidiscrete
*value* at every tilt, with the one-sided probe correction `|t| G`.  This version
needs no measurable tilted optimizer and therefore applies at every real tilt. -/
theorem integral_bipartite_dirichlet_tilted_value_le
    {μ : Measure S} [IsProbabilityMeasure μ]
    {ν : Measure T} [IsProbabilityMeasure ν] [NullSingletonClass ν]
    [StandardBorelSpace S] [StandardBorelSpace T] [MeasurableEq T]
    {q : ℕ} {cost : S → T → ℝ} {C : ℝ}
    (hEnergy : PopulationUniformEnergyBound μ ν q cost C)
    (hcostm : Measurable (Function.uncurry cost))
    (hcost : Integrable (Function.uncurry cost) (μ.prod ν))
    (hhat : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ cost x y - cost x z)))
    {probe : S → T → ℝ} (hprobem : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobe : ∀ x y, |probe x y| ≤ G) (t : ℝ) :
    let ρ : Measure (Fin (m + 1) → T) := Measure.pi (fun _ : Fin (m + 1) ↦ ν)
    let P := ρ.prod (dirichletOne m)
    let k : ℝ := ((m + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))
    Integrable (fun z : (Fin (m + 1) → T) × (Fin (m + 1) → ℝ) ↦
      semidiscreteValue μ (fun s j ↦ k * cost s (z.1 j) + t * probe s (z.1 j))
        z.2) P ∧
    (∫ z, semidiscreteValue μ
      (fun s j ↦ k * cost s (z.1 j) + t * probe s (z.1 j)) z.2 ∂P) ≤
      C + |t| * (G : ℝ) := by
  let ρ : Measure (Fin (m + 1) → T) := Measure.pi (fun _ : Fin (m + 1) ↦ ν)
  let P : Measure ((Fin (m + 1) → T) × (Fin (m + 1) → ℝ)) :=
    ρ.prod (dirichletOne m)
  let k : ℝ := ((m + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))
  have hk : 0 < k := Real.rpow_pos_of_pos (by positivity) _
  have hkne : k ≠ 0 := hk.ne'
  let base : (Fin (m + 1) → T) → S → Fin (m + 1) → ℝ :=
    fun y s j ↦ k * cost s (y j)
  have hpair (j : Fin (m + 1)) :
      MeasurePreserving (fun z : (Fin (m + 1) → T) × S ↦ (z.2, z.1 j))
        (ρ.prod μ) (μ.prod ν) :=
    Measure.measurePreserving_swap.comp
      ((measurePreserving_eval (fun _ : Fin (m + 1) ↦ ν) j).prod
        (MeasurePreserving.id μ))
  have hcij (j : Fin (m + 1)) :
      Integrable (fun z : (Fin (m + 1) → T) × S ↦ k * cost z.2 (z.1 j))
        (ρ.prod μ) :=
    ((hpair j).integrable_comp_of_integrable hcost).const_mul k
  have hmeasc (j : Fin (m + 1)) :
      Measurable (fun z : (Fin (m + 1) → T) × S ↦ k * cost z.2 (z.1 j)) :=
    (hcostm.comp (measurable_snd.prodMk
      ((measurable_pi_apply j).comp measurable_fst))).const_mul k
  have hcg (j : Fin (m + 1)) :
      Measurable (fun z : (Fin (m + 1) → T) × S ↦ probe z.2 (z.1 j)) :=
    hprobem.comp (measurable_snd.prodMk
      ((measurable_pi_apply j).comp measurable_fst))
  have hcz : ∀ᵐ z ∂P, ∀ j, Integrable (fun s ↦ base z.1 s j) μ :=
    measurePreserving_fst.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j ↦ (hcij j).prod_right_ae))
  have hger : ∀ᵐ z ∂P, ∀ j, Integrable (fun s ↦ probe s (z.1 j)) μ := by
    apply Eventually.of_forall
    intro z j
    apply (integrable_const (G : ℝ)).mono'
      (hprobem.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact Eventually.of_forall fun s ↦ by
      simpa only [Function.uncurry, Function.comp_apply, id_eq, Real.norm_eq_abs]
        using hprobe s (z.1 j)
  have hp : ∀ᵐ z ∂P, z.2 ∈ stdSimplex ℝ (Fin (m + 1)) :=
    measurePreserving_snd.quasiMeasurePreserving.ae (ae_mem_stdSimplex_dirichletOne m)
  have hhat' : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ k * cost x y - k * cost x z)) := by
    intro y z hyz
    have hm1 : Measurable (fun x : S ↦ cost x y) :=
      hcostm.comp (measurable_id.prodMk measurable_const)
    have hm2 : Measurable (fun x : S ↦ cost x z) :=
      hcostm.comp (measurable_id.prodMk measurable_const)
    have heq : (fun x : S ↦ k * cost x y - k * cost x z) =
        (fun x : S ↦ k * (cost x y - cost x z)) := by
      funext x
      ring
    rw [heq]
    exact nullSingletonClass_map_mul (hm1.sub hm2) (hhat y z hyz) hkne
  have hat : ∀ᵐ y ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ k * cost s (y j) - k * cost s (y l))) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (m + 1)) ν]
      with y hy
    exact fun j l hjl ↦ hhat' (y j) (y l) (hy.ne hjl)
  have hbase_int : Integrable (fun z : (Fin (m + 1) → T) ×
      (Fin (m + 1) → ℝ) ↦ semidiscreteValue μ (base z.1) z.2) P := by
    simpa only [P, base] using
      integrable_parameterized_dirichlet_semidiscreteValue (m := m) (S := S)
        (V := Fin (m + 1) → T) μ ρ (fun y j s ↦ k * cost s (y j))
        (fun j ↦ hmeasc j) hcij hat
  have htilt_int : Integrable (fun z : (Fin (m + 1) → T) ×
      (Fin (m + 1) → ℝ) ↦ semidiscreteValue μ
        (fun s j ↦ k * cost s (z.1 j) + t * probe s (z.1 j)) z.2) P := by
    simpa only [P] using
      integrable_parameterized_dirichlet_semidiscreteValue_tilt (m := m)
        (S := S) (V := Fin (m + 1) → T) μ ρ
        (fun y j s ↦ k * cost s (y j)) (fun y j s ↦ probe s (y j))
        (fun j ↦ hmeasc j) hcij (fun j ↦ hcg j) hat G
        (fun y s j ↦ hprobe s (y j)) t
  have hineq : ∀ᵐ z ∂P, semidiscreteValue μ
      (fun s j ↦ k * cost s (z.1 j) + t * probe s (z.1 j)) z.2 ≤
      semidiscreteValue μ (base z.1) z.2 + |t| * (G : ℝ) := by
    filter_upwards [hp, hcz, hger] with z hzp hzint hgint
    have hlip := lipschitzWith_semidiscreteValue_tilt μ (base z.1)
      (fun s j ↦ probe s (z.1 j)) hzint hgint G
      (Eventually.of_forall fun s ↦ fun j ↦ hprobe s (z.1 j)) z.2 hzp
    have hdist := hlip.dist_le_mul t 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at hdist
    have hdist' : |semidiscreteValue μ
          (fun s j ↦ base z.1 s j + t * probe s (z.1 j)) z.2 -
        semidiscreteValue μ (base z.1) z.2| ≤ (G : ℝ) * |t| := by
      simpa only [zero_mul, add_zero] using hdist
    have hle := (abs_le.mp hdist').2
    have hG : (G : ℝ) * |t| = |t| * (G : ℝ) := mul_comm _ _
    linarith
  have hsd_le : (∫ z, semidiscreteValue μ (base z.1) z.2 ∂P) ≤ C := by
    have hmean := integral_bipartite_pressure_eq_dirichlet_semidiscreteValue
      (m := m) μ ν (fun x y ↦ k * cost x y) (fun _ _ ↦ (0 : ℝ))
      (hcostm.const_mul k) (hcost.const_mul k) measurable_const hhat' 0 (by simp) 0
    let f : (Fin (m + 1) → S) × (Fin (m + 1) → T) → ℝ := fun ξ ↦
      perturbedAssignmentValue (fun i j ↦ k * cost (ξ.1 i) (ξ.2 j))
        (fun _ _ ↦ (0 : ℝ)) 0 / (m + 1 : ℕ)
    have hD_le : (∫ y, ∫ p, semidiscreteValue μ (fun s j ↦ k * cost s (y j)) p
        ∂dirichletOne m ∂ρ) ≤ C := by
      calc
        (∫ y, ∫ p, semidiscreteValue μ (fun s j ↦ k * cost s (y j)) p
            ∂dirichletOne m ∂ρ)
            = ∫ q : (Fin (m + 1) → T) × (Fin (m + 1) → S),
                perturbedAssignmentValue (fun i j ↦ k * cost (q.2 i) (q.1 j))
                  (fun _ _ ↦ (0 : ℝ)) 0 / (m + 1 : ℕ)
                  ∂(ρ.prod (Measure.pi (fun _ : Fin (m + 1) ↦ μ))) := by
              simpa only [ρ, zero_mul, add_zero] using hmean.2.symm
        _ = ∫ ξ : (Fin (m + 1) → S) × (Fin (m + 1) → T), f ξ
              ∂((Measure.pi (fun _ : Fin (m + 1) ↦ μ)).prod
                (Measure.pi (fun _ : Fin (m + 1) ↦ ν))) :=
            integral_prod_swap f
        _ ≤ C := by
            have hzero := (hEnergy (m + 1) (Nat.succ_pos m)).1.2
            dsimp only at hzero
            have hf_eq : (∫ ξ : (Fin (m + 1) → S) × (Fin (m + 1) → T), f ξ
                  ∂((Measure.pi (fun _ : Fin (m + 1) ↦ μ)).prod
                    (Measure.pi (fun _ : Fin (m + 1) ↦ ν)))) =
                ∫ ξ : (Fin (m + 1) → S) × (Fin (m + 1) → T),
                  perturbedAssignmentValue (fun i j ↦ k * cost (ξ.1 i) (ξ.2 j))
                    0 0 / (m + 1 : ℕ)
                  ∂((Measure.pi (fun _ : Fin (m + 1) ↦ μ)).prod
                    (Measure.pi (fun _ : Fin (m + 1) ↦ ν))) := by
              apply integral_congr_ae
              filter_upwards with ξ
              simp only [f, k, perturbedAssignmentValue, perturbedEdgeCost_zero]
            rw [hf_eq]
            exact hzero
    calc
      (∫ z, semidiscreteValue μ (base z.1) z.2 ∂P)
          = ∫ y, ∫ p, semidiscreteValue μ (base y) p
              ∂dirichletOne m ∂ρ := integral_prod _ hbase_int
      _ = ∫ y, ∫ p, semidiscreteValue μ (fun s j ↦ k * cost s (y j)) p
              ∂dirichletOne m ∂ρ := rfl
      _ ≤ C := hD_le
  refine ⟨htilt_int, ?_⟩
  have hconst : Integrable
      (fun _z : (Fin (m + 1) → T) × (Fin (m + 1) → ℝ) ↦
        |t| * (G : ℝ)) P := integrable_const _
  have hmono := integral_mono_ae htilt_int (hbase_int.add hconst) hineq
  calc
    (∫ z, semidiscreteValue μ
        (fun s j ↦ k * cost s (z.1 j) + t * probe s (z.1 j)) z.2 ∂P)
        ≤ ∫ z, (semidiscreteValue μ (base z.1) z.2 + |t| * (G : ℝ)) ∂P := hmono
    _ = (∫ z, semidiscreteValue μ (base z.1) z.2 ∂P) + |t| * (G : ℝ) := by
        rw [integral_add hbase_int hconst]
        simp
    _ ≤ C + |t| * (G : ℝ) := add_le_add hsd_le le_rfl

end OTSelector.Reconstruction
