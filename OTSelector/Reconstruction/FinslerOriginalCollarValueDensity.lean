import OTSelector.Reconstruction.FinslerOriginalDegenerateScreeningApproximation
import OTSelector.Reconstruction.FinslerRelativeLawLegalRepair
import OTSelector.Reconstruction.MarkedStationaryValueLegalReserveRemovalHall

/-!
# Poisson reserve completion for the collar value density

The remaining CollarValueDensity input of
FinslerOriginalDegenerateScreeningApproximation is supplied by the paper's
reserve construction: dilate the weighted minimizer to intensity lambda,
superpose an independent reserve of intensity rho, and complete the retained
core to a maximum-cardinality matching of the full input while keeping every
retained edge.  This module formalizes the finite augmentation step of that
construction, with its explicit added cost, and isolates the exact remaining
sub-gap.

1. Finite cost algebra.  The total cost of a legal completion splits into the
   retained core cost and the added-edge cost (cost_eq_add_cost_sdiff), and the
   number of added edges is at most the number of free source rows
   (legalMaximumCard_residual_le), so the added cost is at most that count times
   any one-sided edge bound.

2. Poisson reserve completion with explicit added cost.  Under the actual
   reserve clock slack and reserve budget (the reserve count conditions proved
   for the original Poisson reserve in
   MarkedStationaryValueLegalReserveRemovalHall), the exact legal residual
   capacity holds (legal_capacity_of_reserve_slack), and the legal repair of
   FinslerRelativeLawLegalRepair completes every retained legal core to a
   maximum-cardinality legal matching of the full finite input, preserving all
   retained edges, with added cost at most (m - core.card) times the ambient
   edge bound (exists_legal_reserve_completion_with_cost).  This is the finite
   augmentation step of prop:general-finite-path-screening.

3. Exact remaining sub-gap.  The paper integrates the finite completion over the
   Poisson scene law and sends the box size to infinity, producing the
   finite-value comparison p_A <= I_w + C rho^{1-2/q}.  The module records the
   exact consequence: if the actual legal maximum-cardinality finite pressure
   limit p_A is at most the weighted stationary value, then the two stationary
   legal values coincide
   (weightedInf_eq_secondMomentInf_of_legalPressureLimit_le).  The integration
   over the scene law, the reserve superposition/rerooting commutation and the
   box limit are the remaining sub-gap; the finite combinatorial completion and
   its cost bound are proved here.

## Remaining gap

The single missing step is the measurable, stationary lifting of the a.e. finite
reserve completion to the scene law of the weighted matching (preserving the
original independent input law and stationarity), followed by the normalized box
limit.  All finite augmentation, capacity, residual-cost and collar coercivity
interfaces are now closed.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

namespace PartialMatching

variable {m n : ℕ}

/-- The cost of a legal completion splits into the retained core cost and the
added-edge cost. -/
theorem cost_eq_add_cost_sdiff
    {σ τ : PartialMatching m n} (hsub : σ.edges ⊆ τ.edges)
    (c : Fin m → Fin n → ℝ) :
    OTSelector.PartialMatching.cost c τ =
      OTSelector.PartialMatching.cost c σ +
        ∑ e ∈ (τ.edges \ σ.edges), c e.1 e.2 := by
  have hdis : Disjoint σ.edges (τ.edges \ σ.edges) := Finset.disjoint_sdiff
  have hun : σ.edges ∪ (τ.edges \ σ.edges) = τ.edges :=
    Finset.union_sdiff_of_subset hsub
  have hsplit : ∑ e ∈ τ.edges, c e.1 e.2 =
      ∑ e ∈ σ.edges, c e.1 e.2 +
        ∑ e ∈ (τ.edges \ σ.edges), c e.1 e.2 := by
    conv_lhs => rw [← hun]
    rw [Finset.sum_union hdis]
  rw [show OTSelector.PartialMatching.cost c τ = ∑ e ∈ τ.edges, c e.1 e.2 from rfl,
    show OTSelector.PartialMatching.cost c σ = ∑ e ∈ σ.edges, c e.1 e.2 from rfl,
    hsplit]

/-- The number of free source rows of a partial matching is the number of
unmatched sources. -/
theorem freeRows_card (σ : PartialMatching m n) :
    (OTSelector.PartialMatching.freeRows σ).card = m - σ.card := by
  unfold OTSelector.PartialMatching.freeRows
  rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
    ← OTSelector.PartialMatching.card_rows σ]

/-- The residual legal maximum on the unused endpoints is at most the number of
free source rows. -/
theorem legalMaximumCard_residual_le (allowed : Finset (Fin m × Fin n))
    (σ : PartialMatching m n) :
    legalMaximumCard (residualAllowed allowed σ) ≤ m - σ.card := by
  obtain ⟨ρ, hρ, hρcard⟩ := exists_legalMaximumCard (residualAllowed allowed σ)
  have hsub : ρ.rows ⊆ OTSelector.PartialMatching.freeRows σ := by
    intro i hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (hρ he)).2.1⟩
  have hrows : ρ.rows.card ≤ (OTSelector.PartialMatching.freeRows σ).card :=
    Finset.card_le_card hsub
  calc legalMaximumCard (residualAllowed allowed σ) = ρ.card := hρcard.symm
    _ = ρ.rows.card := (OTSelector.PartialMatching.card_rows ρ).symm
    _ ≤ (OTSelector.PartialMatching.freeRows σ).card := hrows
    _ = m - σ.card := freeRows_card σ

/-- **Poisson reserve completion with explicit added cost.**  On a finite adapted
clock scene, the actual reserve slack and reserve budget construct a
maximum-cardinality legal completion of the full finite input which preserves
every edge of the retained legal core, and whose added cost is at most the
number of added edges times the ambient one-sided edge bound.  The added edges
use only the actual unused endpoints (residualAllowed). -/
theorem exists_legal_reserve_completion_with_cost
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (RS : Finset (Fin m)) (RT : Finset (Fin n)) (K : Set ℝ)
    (hK : ∀ i ∈ OTSelector.PartialMatching.freeRows σ, source i ∈ K) (H : ℝ)
    (hslack : ∀ c ∈ K, H ≤ ((RT.filter (fun j => c < target j)).card : ℝ) -
      ((RS.filter (fun i => c ≤ source i)).card : ℝ))
    (hbudget : ((OTSelector.PartialMatching.freeRows σ \ RS).card : ℝ) +
      ((RT \ OTSelector.PartialMatching.freeCols σ).card : ℝ) ≤ H)
    (cost : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, cost i j ≤ B) :
    ∃ τ : PartialMatching m n,
      IsLegal (scalarClockLegalGraph source target) τ ∧ τ.card = m ∧
        σ.edges ⊆ τ.edges ∧
        OTSelector.PartialMatching.cost cost τ ≤
          OTSelector.PartialMatching.cost cost σ +
            ((m - σ.card : ℕ) : ℝ) * B := by
  obtain ⟨hmax, hcap⟩ :=
    legal_capacity_of_reserve_slack source target σ hσ RS RT K hK H hslack hbudget
  have hcapacity : σ.card +
      legalMaximumCard (residualAllowed (scalarClockLegalGraph source target) σ) =
        legalMaximumCard (scalarClockLegalGraph source target) := by
    rw [hmax]
    exact hcap
  obtain ⟨τ, hτ, hτcard, hsub, hτcost⟩ :=
    exists_legal_completion_of_residual_capacity σ hσ hcapacity cost
  have hres : OTSelector.PartialMatching.cost cost τ =
      OTSelector.PartialMatching.cost cost σ +
        ∑ e ∈ (τ.edges \ σ.edges), cost e.1 e.2 :=
    cost_eq_add_cost_sdiff hsub cost
  have hadd : ∑ e ∈ (τ.edges \ σ.edges), cost e.1 e.2 ≤
      ((m - σ.card : ℕ) : ℝ) * B := by
    rw [hτcost]
    obtain ⟨ρ, hρ, hρcard, hρcost⟩ :=
      exists_cost_eq_legalMaximumValue
        (residualAllowed (scalarClockLegalGraph source target) σ) cost
    rw [← hρcost]
    calc OTSelector.PartialMatching.cost cost ρ
        ≤ (ρ.card : ℝ) * B := OTSelector.PartialMatching.cost_le_card_mul cost ρ hB
      _ = ((legalMaximumCard (residualAllowed (scalarClockLegalGraph source target) σ) : ℕ) : ℝ) * B := by
          rw [hρcard]
      _ ≤ ((m - σ.card : ℕ) : ℝ) * B := by
          exact mul_le_mul_of_nonneg_right
            (Nat.cast_le.mpr (legalMaximumCard_residual_le _ σ)) hB0
  exact ⟨τ, hτ, by rw [hτcard, hmax], hsub, by rw [hres]; linarith⟩

end PartialMatching

/-! ## Exact remaining sub-gap: the finite-value comparison -/

section FinitePressureComparison

open Module Manifold OTSelector.Geometry ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- **The finite-value comparison is exactly the remaining value identification.**
If a limit p of the actual legal maximum-cardinality finite pressures is at most
the weighted stationary legal value, then the weighted and second-moment
stationary legal values coincide.  The paper obtains this upper comparison from
the reserve construction after integrating the finite completion over the
Poisson scene law and sending the box size to infinity; the finite combinatorial
completion and its cost bound are proved above. -/
theorem weightedInf_eq_secondMomentInf_of_legalPressureLimit_le
    {I : Set ℝ} {δ : ℝ} (Dbins : FiniteScalarBins I δ) (hδ : 0 < δ)
    (hIm : MeasurableSet I)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hpi : Vlasov.IsCoupling pi α β)
    (hI : ∀ᵐ z ∂pi, z.1 ∈ I ∧ z.2 ∈ I) (hgap : ∀ᵐ z ∂pi, δ ≤ z.2 - z.1)
    (hsep : ∀ᵐ z ∂α.prod β, δ ≤ |z.2 - z.1|)
    (q : ℕ) (hq : 4 < q)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ => kin z.1 z.2)))
    (hkn : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hkb : ∀ a b (v : Fin q → ℝ), |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (hgc : ContinuousOn (Function.uncurry g) K)
    {p : ℝ → ℝ}
    (hp : ∀ t : ℝ, Tendsto (fun R : ℝ =>
      legalMarkedScalePressure q id id α β kin g R t) atTop (𝓝 (p t)))
    (t : ℝ) (hle : p t ≤ legalWeightedInf q α β kin g t) :
    legalWeightedInf q α β kin g t = legalSecondMomentInf q α β kin g t := by
  obtain ⟨p₀, hp₀, hbounds⟩ :=
    exists_legalPressureLimit_ge_weighted_le_secondMoment Dbins hδ hIm pi α β hpi
      hI hgap hsep q hq hC hG hk hkn hkb hhom hg hgb hA hB hα hβ hK matrix
      hmatrix hpos hlegal hactual hgc
  have hp_eq : p₀ = p := funext fun s => tendsto_nhds_unique (hp₀ s) (hp s)
  have hlow : legalWeightedInf q α β kin g t ≤ legalSecondMomentInf q α β kin g t :=
    (hbounds t).1
  have hup : legalSecondMomentInf q α β kin g t ≤ p₀ t := (hbounds t).2
  rw [hp_eq] at hup
  exact le_antisymm hlow (hup.trans hle)

end FinitePressureComparison

end OTSelector.Reconstruction


namespace OTSelector.Reconstruction

/-! ## A fully coercive collar closes the value identification -/

section FullMassCollar

open Module Manifold OTSelector.Geometry ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- If a coercive product collar captures the two original clock laws up to
null sets, then every weighted stationary matching has its true Palm pair
heights in the collar, hence is a finite-second-moment matching. -/
theorem secondMomentSubclass_of_full_mass_collar
    (D : OriginalSeedConditionalMoments S w μ ν)
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAmass : μ Aᶜ = 0) (hBmass : ν Bᶜ = 0)
    {c : ℝ} (hc : 0 < c)
    (hLB : ∀ a ∈ A, ∀ b ∈ B, a < b →
      ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
        c * ‖v‖ ^ 2 ≤ D.originalFocalKinetic gap a b v)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    Q.secondMomentSubclass := by
  have hzero : legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
      {m | m.1 ∉ A ×ˢ B} = 0 := by
    refine le_antisymm ?_ bot_le
    have hle := palm_mass_outside_collar_le Q hA hB
    rwa [hAmass, hBmass, add_zero] at hle
  have hsupp : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      m.1 ∈ A ×ˢ B := by
    rw [ae_iff]
    exact hzero
  refine secondMomentSubclass_of_collar D (C := A ×ˢ B) hc ?_ Q hsupp
  intro p hp hpq v
  exact hLB p.1 hp.1 p.2 hp.2 hpq v

/-- **Fully coercive collar: the degenerate value identification is closed.**  If
the original clock laws are carried by one compact collar on which the focal
coefficient is uniformly positive definite, then the second-moment subclass is
the entire weighted class and I_w = I_2 unconditionally. -/
theorem originalSecondMomentSubclass_eq_univ_of_full_mass_collar
    (D : OriginalSeedConditionalMoments S w μ ν)
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAmass : μ Aᶜ = 0) (hBmass : ν Bᶜ = 0)
    {c : ℝ} (hc : 0 < c)
    (hLB : ∀ a ∈ A, ∀ b ∈ B, a < b →
      ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
        c * ‖v‖ ^ 2 ≤ D.originalFocalKinetic gap a b v) :
    D.originalSecondMomentSubclass gap g = Set.univ := by
  ext Q
  exact ⟨fun _ => trivial, fun _ =>
    secondMomentSubclass_of_full_mass_collar D hA hB hAmass hBmass hc hLB Q⟩

/-- **Fully coercive collar: I_w = I_2 unconditionally.** -/
theorem originalWeightedStationaryInf_eq_secondMomentInf_of_full_mass_collar
    (D : OriginalSeedConditionalMoments S w μ ν)
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAmass : μ Aᶜ = 0) (hBmass : ν Bᶜ = 0)
    {c : ℝ} (hc : 0 < c)
    (hLB : ∀ a ∈ A, ∀ b ∈ B, a < b →
      ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
        c * ‖v‖ ^ 2 ≤ D.originalFocalKinetic gap a b v) (t : ℝ) :
    D.originalWeightedStationaryInf gap g t =
      D.originalSecondMomentStationaryInf gap g t := by
  have huniv : D.originalSecondMomentSubclass gap g = Set.univ :=
    originalSecondMomentSubclass_eq_univ_of_full_mass_collar D (g := g) hA hB
      hAmass hBmass hc hLB
  have hsecond : D.originalSecondMomentStationaryInf gap g t =
      sInf (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)) := by
    simp only [OriginalSeedConditionalMoments.originalSecondMomentStationaryInf, huniv,
      Set.image_univ]
  rw [hsecond]
  rfl

end FullMassCollar

end OTSelector.Reconstruction

