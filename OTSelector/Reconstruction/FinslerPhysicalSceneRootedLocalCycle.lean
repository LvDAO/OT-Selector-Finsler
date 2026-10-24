import OTSelector.Reconstruction.FinslerPhysicalSceneRootedGlobal
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClock
import OTSelector.Probability.CavitySemidiscretePlanBlocks

/-!
# Original global optimality on the same actual source restriction

A competitor on a physical source set is glued to the original allocation on
its complement. Global optimality therefore forces local optimality with the
actual restricted column masses, for the same physical or tilted cost.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-- The retained target columns are the original coefficients integrated over
the same physical source set. -/
def physicalSceneRestrictedColumns (μ : Measure M) (H : Set M)
    (a : M → Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ := ∫ x in H, a x j ∂μ

/-- Source restriction retains the original allocation and its exact columns. -/
theorem isSemidiscreteAllocation_physicalScene_restrict
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (H : Set M) :
    IsSemidiscreteAllocation (μ.restrict H) (physicalSceneRestrictedColumns μ H a) a :=
  ⟨fun j ↦ (ha.integrable j).integrableOn, ae_restrict_of_ae ha.nonneg,
    ae_restrict_of_ae ha.sum_one, fun _ ↦ rfl⟩

/-- Any competitor for the actual retained columns is a genuine global
competitor when glued to the original allocation outside the physical set. -/
theorem isSemidiscreteAllocation_physicalScene_piecewise
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (H : Set M) (hH : MeasurableSet H)
    (b : M → Fin (n + 1) → ℝ)
    (hb : IsSemidiscreteAllocation (μ.restrict H) (physicalSceneRestrictedColumns μ H a) b) :
    IsSemidiscreteAllocation μ p (H.piecewise b a) := by
  have hpi j : (fun x ↦ H.piecewise b a x j) =
      H.piecewise (fun x ↦ b x j) (fun x ↦ a x j) := by
    funext x
    by_cases hx : x ∈ H <;> simp [hx]
  have hin j : Integrable (fun x ↦ H.piecewise b a x j) μ := by
    rw [hpi]
    exact Integrable.piecewise hH (hb.integrable j) (ha.integrable j).integrableOn
  refine ⟨hin, ?_, ?_, ?_⟩
  · filter_upwards [ha.nonneg, (ae_restrict_iff' hH).mp hb.nonneg] with x hax hbx
    by_cases hx : x ∈ H
    · simpa only [piecewise_eq_of_mem H b a hx] using hbx hx
    · simpa only [piecewise_eq_of_notMem H b a hx] using hax
  · filter_upwards [ha.sum_one, (ae_restrict_iff' hH).mp hb.sum_one] with x hax hbx
    by_cases hx : x ∈ H
    · simpa only [piecewise_eq_of_mem H b a hx] using hbx hx
    · simpa only [piecewise_eq_of_notMem H b a hx] using hax
  · intro j
    rw [hpi]
    rw [integral_piecewise hH (hb.integrable j) (ha.integrable j).integrableOn,
      hb.mass j]
    change (∫ x in H, a x j ∂μ) + (∫ x in Hᶜ, a x j ∂μ) = p j
    rw [integral_add_compl hH (ha.integrable j), ha.mass j]

/-- Gluing changes the global original objective by exactly its actual
restricted objective change; there is no normalization or new target law. -/
theorem semidiscreteAllocationCost_physicalScene_piecewise
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (H : Set M) (hH : MeasurableSet H)
    (b : M → Fin (n + 1) → ℝ)
    (hb : IsSemidiscreteAllocation (μ.restrict H) (physicalSceneRestrictedColumns μ H a) b)
    (c : M → Fin (n + 1) → ℝ) (hc : ∀ j, Integrable (fun x ↦ c x j) μ) :
    semidiscreteAllocationCost μ c (H.piecewise b a) =
      semidiscreteAllocationCost (μ.restrict H) c b +
        semidiscreteAllocationCost (μ.restrict Hᶜ) c a := by
  have hia : Integrable (fun x ↦ ∑ j, a x j * c x j) μ :=
    integrable_finsetSum _ (fun j _ ↦ ha.integrable_mul c hc j)
  have hib : Integrable (fun x ↦ ∑ j, b x j * c x j) (μ.restrict H) :=
    integrable_finsetSum _ (fun j _ ↦ hb.integrable_mul c
      (fun k ↦ (hc k).integrableOn) j)
  have heq (x : M) : (∑ j, H.piecewise b a x j * c x j) =
      H.piecewise (fun x ↦ ∑ j, b x j * c x j) (fun x ↦ ∑ j, a x j * c x j) x := by
    by_cases hx : x ∈ H <;> simp [hx]
  simp only [semidiscreteAllocationCost, heq]
  exact integral_piecewise hH hib hia.integrableOn

/-- Original global optimality produces optimality on every measurable physical
source restriction, with the original exact random retained columns. -/
theorem isOptimalSemidiscreteAllocation_physicalScene_restrict
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a c : M → Fin (n + 1) → ℝ}
    (hopt : IsOptimalSemidiscreteAllocation μ p c a)
    (hc : ∀ j, Integrable (fun x ↦ c x j) μ)
    (H : Set M) (hH : MeasurableSet H) :
    IsOptimalSemidiscreteAllocation (μ.restrict H)
      (physicalSceneRestrictedColumns μ H a) c a := by
  refine ⟨isSemidiscreteAllocation_physicalScene_restrict hopt.1 H, ?_⟩
  intro b hb
  have hglobal := hopt.2 (H.piecewise b a)
    (isSemidiscreteAllocation_physicalScene_piecewise hopt.1 H hH b hb)
  rw [semidiscreteAllocationCost_physicalScene_piecewise hopt.1 H hH b hb c hc] at hglobal
  have hcost : semidiscreteAllocationCost μ c a =
      semidiscreteAllocationCost (μ.restrict H) c a +
        semidiscreteAllocationCost (μ.restrict Hᶜ) c a := by
    exact (integral_add_compl hH
      (integrable_finsetSum _ (fun j _ ↦ hopt.1.integrable_mul c hc j))).symm
  rw [hcost] at hglobal
  exact le_of_add_le_add_right hglobal

/-- Exact actual rectangle masses after restricting the original physical
source and observing both original endpoints at the same root. -/
theorem physicalSceneRootedPlan_allocation_restrict_prod
    {ι : Type*} [Fintype ι]
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (Y : Fin (n + 1) → M)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (A B : Set ((ι → ℝ) × ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    physicalSceneRootedPlan ((physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ univ))
      coord u N z (A ×ˢ B) =
      ENNReal.ofReal N * ENNReal.ofReal (semidiscreteBlockMass μ a
        (H ∩ (fun x ↦ (coord x - z, u x)) ⁻¹' A)
        (Finset.univ.filter (fun j ↦ (coord (Y j) - z, u (Y j)) ∈ B))) := by
  let f := fun x ↦ (coord x - z, u x)
  have hf : Measurable f := (hcoord.sub measurable_const).prodMk hu
  have haH := isSemidiscreteAllocation_physicalScene_restrict ha H
  rw [← physicalSceneAllocationPlan_restrict μ a Y hH]
  unfold physicalSceneRootedPlan physicalSceneAllocationPlan
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_map
    (measurable_physicalSceneRootedObservation coord hcoord u hu z)
    (measurable_id.prodMap (measurable_of_finite Y))]
  have heq : physicalSceneRootedObservation coord u z ∘ Prod.map id Y =
      Prod.map f (f ∘ Y) := rfl
  rw [heq, haH.map_allocationMeasure_prod f hf (f ∘ Y) A B hA hB]
  congr 2
  unfold semidiscreteBlockMass
  apply Finset.sum_congr rfl
  intro j hj
  rw [Measure.restrict_restrict (hA.preimage hf), inter_comm]

/-- A strict certificate in the SAME original physical or tilted cost cannot
have positive mass in both actual restricted rooted rectangles. This follows
from original global optimality and an internally constructed exchange. -/
theorem physicalSceneRootedPlan_original_optimal_strict_rectangle_min_eq_zero
    {ι : Type*} [Fintype ι]
    {μ : Measure M} [SFinite μ] {p : Fin (n + 1) → ℝ}
    {a c : M → Fin (n + 1) → ℝ}
    (hopt : IsOptimalSemidiscreteAllocation μ p c a)
    (hc : ∀ j, Integrable (fun x ↦ c x j) μ)
    (Y : Fin (n + 1) → M) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ x ∈ H, ∀ x' ∈ H,
      (coord x - z, u x) ∈ A₀ → (coord x' - z, u x') ∈ A₁ →
      ∀ j, (coord (Y j) - z, u (Y j)) ∈ B₀ →
      ∀ l, (coord (Y l) - z, u (Y l)) ∈ B₁ →
        ε ≤ c x j + c x' l - c x l - c x' j) :
    min
      (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ univ))
        coord u N z (A₀ ×ˢ B₀))
      (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ univ))
        coord u N z (A₁ ×ˢ B₁)) = 0 := by
  let f := fun x ↦ (coord x - z, u x)
  have hf : Measurable f := (hcoord.sub measurable_const).prodMk hu
  let E₀ := H ∩ f ⁻¹' A₀
  let E₁ := H ∩ f ⁻¹' A₁
  let J := Finset.univ.filter (fun j ↦ f (Y j) ∈ B₀)
  let L := Finset.univ.filter (fun j ↦ f (Y j) ∈ B₁)
  have hE₀ : MeasurableSet E₀ := hH.inter (hA₀.preimage hf)
  have hE₁ : MeasurableSet E₁ := hH.inter (hA₁.preimage hf)
  have hEd : Disjoint E₀ E₁ :=
    (hdisj.preimage f).mono inter_subset_right inter_subset_right
  obtain ⟨b, hb, _, hgain⟩ := exists_semidiscrete_target_block_exchange μ p a c
    hopt.1 hc E₀ E₁ hE₀ hE₁ hEd J L ε (by
      intro x hx x' hx' j hj l hl
      exact hgap x hx.1 x' hx'.1 hx.2 hx'.2 j (Finset.mem_filter.mp hj).2
        l (Finset.mem_filter.mp hl).2)
  have hmass0 : 0 ≤ min (semidiscreteBlockMass μ a E₀ J)
      (semidiscreteBlockMass μ a E₁ L) :=
    le_min (hopt.1.blockMass_nonneg E₀ J) (hopt.1.blockMass_nonneg E₁ L)
  have hmass : min (semidiscreteBlockMass μ a E₀ J)
      (semidiscreteBlockMass μ a E₁ L) = 0 := by
    have hbound := hopt.2 b hb
    have hz : ε * min (semidiscreteBlockMass μ a E₀ J)
        (semidiscreteBlockMass μ a E₁ L) ≤ 0 := by linarith
    exact le_antisymm (by nlinarith) hmass0
  rw [physicalSceneRootedPlan_allocation_restrict_prod hopt.1 Y H hH coord hcoord u hu N z
      A₀ B₀ hA₀ hB₀,
    physicalSceneRootedPlan_allocation_restrict_prod hopt.1 Y H hH coord hcoord u hu N z
      A₁ B₁ hA₁ hB₁]
  change min (ENNReal.ofReal N * ENNReal.ofReal (semidiscreteBlockMass μ a E₀ J))
    (ENNReal.ofReal N * ENNReal.ofReal (semidiscreteBlockMass μ a E₁ L)) = 0
  rw [← mul_min, ← ENNReal.ofReal_min, hmass, ENNReal.ofReal_zero, mul_zero]

/-- The same original almost-sure global optimizers exclude the strict
physical-cost rectangle witness in the actual finite completed plan family.
Both the original random columns and the physical source restriction persist. -/
theorem ae_physicalSceneGlobalAllocationFamily_original_optimal_strict_rectangle
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (a c : Ω → M → Fin (n + 1) → ℝ) (p : Ω → Fin (n + 1) → ℝ)
    (hopt : ∀ᵐ w ∂P, IsOptimalSemidiscreteAllocation μ (p w) (c w) (a w))
    (hc : ∀ᵐ w ∂P, ∀ j, Integrable (fun x ↦ c w x j) μ)
    (Y : Ω → Fin (n + 1) → M) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ᵐ w ∂P, ∀ z : ι → ℝ, ∀ x ∈ H, ∀ x' ∈ H,
      (coord x - z, u x) ∈ A₀ → (coord x' - z, u x') ∈ A₁ →
      ∀ j, (coord (Y w j) - z, u (Y w j)) ∈ B₀ →
      ∀ l, (coord (Y w l) - z, u (Y w l)) ∈ B₁ →
        ε ≤ c w x j + c w x' l - c w x l - c w x' j) :
    ∀ᵐ w ∂P, ∀ z : ι → ℝ,
      min
        (physicalSceneRootedPlan ((physicalSceneGlobalAllocationFamily μ a Y w).restrict
          (H ×ˢ univ)) coord u N z (A₀ ×ˢ B₀))
        (physicalSceneRootedPlan ((physicalSceneGlobalAllocationFamily μ a Y w).restrict
          (H ×ˢ univ)) coord u N z (A₁ ×ˢ B₁)) = 0 := by
  filter_upwards [hopt, hc, hgap,
    physicalSceneGlobalAllocationFamily_ae_eq P μ a Y p (hopt.mono fun _ h ↦ h.1)]
    with w hw hcw hgw heq
  intro z
  rw [heq]
  exact physicalSceneRootedPlan_original_optimal_strict_rectangle_min_eq_zero hw hcw
    (Y w) H hH coord hcoord u hu N z A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hdisj ε hε (hgw z)

end OTSelector.Reconstruction
