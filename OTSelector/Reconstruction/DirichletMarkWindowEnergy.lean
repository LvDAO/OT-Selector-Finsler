import OTSelector.Probability.MarkWindowEnergyBound
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Mark-window bounds from a real Dirichlet allocation energy

The mark-window estimate consumes an `ℝ≥0∞`-valued expected energy, whereas the
Dirichlet energy theorem (`integral_bipartite_dirichlet_tilted_value_le` and its
Finsler instantiation) returns a *real* bound on the expected
`semidiscreteAllocationCost`.  This module performs the bookkeeping that turns
the latter into the former.

The main bridge is `lintegral_ofReal_allocationCost_eq`: for an almost-surely
feasible allocation family, the double `ℝ≥0∞` integral of `ENNReal.ofReal` of the
edge weights equals `ENNReal.ofReal` of the real expected allocation cost.  The
proof rewrites the inner integral with
`lintegral_ofReal_semidiscreteAllocationCost_ae` and then pushes `ofReal` through
the outer integral with `ofReal_integral_eq_lintegral_ofReal`; the latter needs
integrability and almost-sure nonnegativity of the allocation cost.

Specialising to `w ω e = k * slack ω e.1 e.2` and applying the mark-window
adapter `lintegral_rootedPlan_markWindow_le_of_slackEnergy` yields the final
bound with constant `ENNReal.ofReal Creal`.
-/

open MeasureTheory Set
open scoped ENNReal Classical BigOperators

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] {m : ℕ}

/-! ## The real-to-ENNReal bridge -/

/-- For an almost-surely feasible family of semidiscrete allocations, the
`ℝ≥0∞` lintegral of `ENNReal.ofReal` of the edge costs against the allocation
coupling is exactly `ENNReal.ofReal` of the real expected allocation cost. -/
theorem lintegral_ofReal_allocationCost_eq
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (a : Ω → S → Fin (m + 1) → ℝ) (p : Ω → Fin (m + 1) → ℝ)
    (hfeas : ∀ᵐ ω ∂P, IsSemidiscreteAllocation μ (p ω) (fun s ↦ a ω s))
    (c : Ω → S → Fin (m + 1) → ℝ)
    (hcm : ∀ ω, Measurable (Function.uncurry (c ω)))
    (hc : ∀ ω j, Integrable (fun s ↦ c ω s j) μ)
    (hcn : ∀ᵐ ω ∂P, ∀ᵐ s ∂μ, ∀ j, 0 ≤ c ω s j)
    (hcost_int : Integrable (fun ω ↦
      semidiscreteAllocationCost μ (c ω) (fun s ↦ a ω s)) P)
    (hcost_nonneg : 0 ≤ᵐ[P] fun ω ↦
      semidiscreteAllocationCost μ (c ω) (fun s ↦ a ω s)) :
    (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (c ω e.1 e.2)
        ∂semidiscreteAllocationMeasure μ (fun s ↦ a ω s) ∂P) =
      ENNReal.ofReal (∫ ω,
        semidiscreteAllocationCost μ (c ω) (fun s ↦ a ω s) ∂P) := by
  rw [lintegral_ofReal_semidiscreteAllocationCost_ae P μ a p hfeas c hcm hc hcn]
  exact (ofReal_integral_eq_lintegral_ofReal hcost_int hcost_nonneg).symm

/-- The scaled-slack version of the bridge: a real bound `Creal` on the expected
allocation cost of `k * slack` gives the `ℝ≥0∞` energy bound used by the
mark-window adapter. -/
theorem lintegral_ofReal_scaledSlackEnergy_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (a : Ω → S → Fin (m + 1) → ℝ) (p : Ω → Fin (m + 1) → ℝ)
    (hfeas : ∀ᵐ ω ∂P, IsSemidiscreteAllocation μ (p ω) (fun s ↦ a ω s))
    (slack : Ω → S → Fin (m + 1) → ℝ) (k : ℝ)
    (hslackm : ∀ ω, Measurable (Function.uncurry (slack ω)))
    (hc : ∀ ω j, Integrable (fun s ↦ k * slack ω s j) μ)
    (hcn : ∀ᵐ ω ∂P, ∀ᵐ s ∂μ, ∀ j, 0 ≤ k * slack ω s j)
    (hcost_int : Integrable (fun ω ↦
      semidiscreteAllocationCost μ (fun s j ↦ k * slack ω s j)
        (fun s ↦ a ω s)) P)
    (hcost_nonneg : 0 ≤ᵐ[P] fun ω ↦
      semidiscreteAllocationCost μ (fun s j ↦ k * slack ω s j)
        (fun s ↦ a ω s))
    {Creal : ℝ}
    (hbound : (∫ ω, semidiscreteAllocationCost μ
        (fun s j ↦ k * slack ω s j) (fun s ↦ a ω s) ∂P) ≤ Creal) :
    (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (k * slack ω e.1 e.2)
        ∂semidiscreteAllocationMeasure μ (fun s ↦ a ω s) ∂P) ≤
      ENNReal.ofReal Creal := by
  have hcm : ∀ ω, Measurable
      (Function.uncurry (fun s j ↦ k * slack ω s j)) := fun ω ↦
    show Measurable (fun x : S × Fin (m + 1) ↦ k * slack ω x.1 x.2) from
      (hslackm ω).const_mul k
  rw [lintegral_ofReal_allocationCost_eq P μ a p hfeas
    (fun ω s j ↦ k * slack ω s j) hcm hc hcn hcost_int hcost_nonneg]
  exact ENNReal.ofReal_le_ofReal hbound

/-! ## Packaging with the mark-window adapter -/

/-- The mark-window bound obtained from a real expected allocation cost bound.
The threshold is `ENNReal.ofReal (k * delta)` and the energy constant is
`ENNReal.ofReal Creal`. -/
theorem lintegral_rootedPlan_markWindow_le_of_allocationCost
    {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (a : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ham : ∀ j, Measurable (fun v ↦ a v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (N : ℝ) (hN : 0 < N) (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (E : Set (A × B)) (hE : MeasurableSet E)
    (slack : Ω → ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (k delta : ℝ) (hk : 0 < k) (hdelta : 0 < delta)
    (hslackm : ∀ ω, Measurable (Function.uncurry (slack ω)))
    (hgood : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ a (ω, s)) ∧
      ∀ᵐ e ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s)),
        (e.1.2, (Y ω e.2).2) ∈ E → delta ≤ slack ω e.1 e.2)
    (hc : ∀ ω j, Integrable (fun s ↦ k * slack ω s j) μ)
    (hcn : ∀ᵐ ω ∂P, ∀ᵐ s ∂μ, ∀ j, 0 ≤ k * slack ω s j)
    (hcost_int : Integrable (fun ω ↦ semidiscreteAllocationCost μ
      (fun s j ↦ k * slack ω s j) (fun s ↦ a (ω, s))) P)
    (hcost_nonneg : 0 ≤ᵐ[P] fun ω ↦ semidiscreteAllocationCost μ
      (fun s j ↦ k * slack ω s j) (fun s ↦ a (ω, s)))
    {Creal : ℝ}
    (hbound : (∫ ω, semidiscreteAllocationCost μ
      (fun s j ↦ k * slack ω s j) (fun s ↦ a (ω, s)) ∂P) ≤ Creal) :
    (∫⁻ v : Ω × (ι → ℝ),
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2
        (cavityMarkWindow U E)
      ∂P.prod (cavityRootMeasure volume D N)) ≤
      volume U * ENNReal.ofReal Creal / ENNReal.ofReal (k * delta) := by
  have henergy : (∫⁻ ω, ∫⁻ e,
      ENNReal.ofReal (k * slack ω e.1 e.2)
      ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s)) ∂P) ≤
      ENNReal.ofReal Creal :=
    lintegral_ofReal_scaledSlackEnergy_le P μ (fun ω s ↦ a (ω, s)) p
      (hgood.mono fun ω hω ↦ hω.1) slack k hslackm hc hcn hcost_int
      hcost_nonneg hbound
  exact lintegral_rootedPlan_markWindow_le_of_slackEnergy P μ p a ham Y hY N hN
    D U hU hUf E hE slack k delta hk hdelta hslackm hgood
    (ENNReal.ofReal Creal) henergy

end OTSelector.Reconstruction
