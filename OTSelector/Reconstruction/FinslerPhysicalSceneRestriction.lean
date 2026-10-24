import OTSelector.Reconstruction.FinslerPhysicalSceneTransport

/-!
# Restricting the same global allocation to an actual source cell

The allocation coefficients are retained.  Its local column masses are their
actual integrals against the normalized source restriction; no Dirichlet law
for these random masses is asserted.  The unnormalized local plan is exactly
the restriction of the global plan.  Every nonnegative local energy is bounded
by the global energy, with the explicit inverse cell mass after normalization.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

section Restriction

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- The realized column masses of the same allocation on its normalized source cell. -/
def restrictedAllocationMass (μ : Measure X) (H : Set X)
    (a : X → Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℝ :=
  ∫ x, a x j ∂normalizedFiniteLaw (μ.restrict H)

/-- Jointly measurable global coefficients give measurable realized local masses. -/
theorem measurable_restrictedAllocationMass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure X) [IsFiniteMeasure μ]
    (H : Set X) (a : Ω → X → Fin (m + 1) → ℝ)
    (ha : ∀ j, Measurable (fun z : Ω × X ↦ a z.1 z.2 j)) (j : Fin (m + 1)) :
    Measurable (fun w ↦ restrictedAllocationMass μ H (a w) j) :=
  (ha j).stronglyMeasurable.integral_prod_right'.measurable

/-- The same global allocation is feasible on the normalized cell, for exactly
its realized restricted column masses. -/
theorem semidiscreteAllocation_normalized_restrict
    {μ : Measure X} {p : Fin (m + 1) → ℝ} {a : X → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (H : Set X) :
    IsSemidiscreteAllocation (normalizedFiniteLaw (μ.restrict H))
      (restrictedAllocationMass μ H a) a := by
  refine ⟨fun j ↦ ?_, ae_normalizedFiniteLaw (ae_restrict_of_ae ha.nonneg),
    ae_normalizedFiniteLaw (ae_restrict_of_ae ha.sum_one), fun _ ↦ rfl⟩
  exact (ha.integrable j).restrict.smul_measure_nnreal

/-- At positive actual cell mass the realized local masses form a probability
vector, without any further assertion about their distribution. -/
theorem restrictedAllocationMass_mem_stdSimplex
    {μ : Measure X} [IsFiniteMeasure μ] {p : Fin (m + 1) → ℝ}
    {a : X → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (H : Set X) (hmass : 0 < (μ.restrict H).real univ) :
    restrictedAllocationMass μ H a ∈ stdSimplex ℝ (Fin (m + 1)) := by
  have : IsProbabilityMeasure (normalizedFiniteLaw (μ.restrict H)) :=
    normalizedFiniteLaw_probability _ hmass
  have hlocal := semidiscreteAllocation_normalized_restrict ha H
  refine ⟨fun j ↦ integral_nonneg_of_ae (hlocal.nonneg.mono fun x hx ↦ hx j), ?_⟩
  change (∑ j, ∫ x, a x j ∂normalizedFiniteLaw (μ.restrict H)) = 1
  rw [← integral_finsetSum _ (fun j _ ↦ hlocal.integrable j)]
  calc
    _ = ∫ _x, (1 : ℝ) ∂normalizedFiniteLaw (μ.restrict H) :=
      integral_congr_ae hlocal.sum_one
    _ = 1 := by simp

/-- Restricting the source measure restricts the actual allocation plan to that
source cell, without modifying any allocation coefficient. -/
theorem semidiscreteAllocationMeasure_restrict
    (μ : Measure X) (a : X → Fin (m + 1) → ℝ) {H : Set X} (hH : MeasurableSet H) :
    semidiscreteAllocationMeasure (μ.restrict H) a =
      (semidiscreteAllocationMeasure μ a).restrict (H ×ˢ univ) := by
  unfold semidiscreteAllocationMeasure
  have hsum := map_sum (Measure.restrictₗ (H ×ˢ (univ : Set (Fin (m + 1)))))
    (fun j : Fin (m + 1) ↦
      (μ.withDensity (fun x ↦ ENNReal.ofReal (a x j))).map (fun x ↦ (x, j))) Finset.univ
  change (∑ j, _) = _
  rw [show (∑ j, (μ.withDensity (fun x ↦ ENNReal.ofReal (a x j))).map
      (fun x ↦ (x, j))).restrict (H ×ˢ univ) = ∑ j,
        ((μ.withDensity (fun x ↦ ENNReal.ofReal (a x j))).map
          (fun x ↦ (x, j))).restrict (H ×ˢ univ) from hsum]
  apply Finset.sum_congr rfl
  intro j _
  have hm : Measurable (fun x : X ↦ (x, j)) := measurable_id.prodMk measurable_const
  rw [Measure.restrict_map hm
    (hH.prod MeasurableSet.univ)]
  have hpre : (fun x : X ↦ (x, j)) ⁻¹' (H ×ˢ (univ : Set (Fin (m + 1)))) = H := by
    ext x
    simp
  rw [hpre, restrict_withDensity hH]

/-- Scaling the physical source scales its entire allocation plan. -/
theorem semidiscreteAllocationMeasure_smul (μ : Measure X)
    (a : X → Fin (m + 1) → ℝ) (c : ℝ≥0∞) :
    semidiscreteAllocationMeasure (c • μ) a = c • semidiscreteAllocationMeasure μ a := by
  unfold semidiscreteAllocationMeasure
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [withDensity_smul_measure, Measure.map_smul]

/-- The normalized local plan is the same global plan restriction multiplied by
the inverse actual cell mass. -/
theorem semidiscreteAllocationMeasure_normalized_restrict
    (μ : Measure X) (a : X → Fin (m + 1) → ℝ) {H : Set X} (hH : MeasurableSet H) :
    semidiscreteAllocationMeasure (normalizedFiniteLaw (μ.restrict H)) a =
      (((μ.restrict H).real univ)⁻¹.toNNReal : ℝ≥0∞) •
        (semidiscreteAllocationMeasure μ a).restrict (H ×ˢ univ) := by
  change semidiscreteAllocationMeasure
    ((((μ.restrict H).real univ)⁻¹.toNNReal : ℝ≥0∞) • μ.restrict H) a = _
  rw [semidiscreteAllocationMeasure_smul,
    semidiscreteAllocationMeasure_restrict μ a hH]

/-- Every nonnegative energy of the normalized local plan is bounded by the
same global plan energy times the inverse cell mass. -/
theorem lintegral_normalized_restricted_allocation_le
    (μ : Measure X) (a : X → Fin (m + 1) → ℝ) {H : Set X} (hH : MeasurableSet H)
    (energy : X × Fin (m + 1) → ℝ≥0∞) :
    (∫⁻ e, energy e ∂semidiscreteAllocationMeasure (normalizedFiniteLaw (μ.restrict H)) a) ≤
      (((μ.restrict H).real univ)⁻¹.toNNReal : ℝ≥0∞) *
        ∫⁻ e, energy e ∂semidiscreteAllocationMeasure μ a := by
  rw [semidiscreteAllocationMeasure_normalized_restrict μ a hH, lintegral_smul_measure,
    smul_eq_mul]
  gcongr
  exact Measure.restrict_le_self

/-- The same energy comparison holds in the original random environment, with
its unchanged realized column masses and the same deterministic source cell. -/
theorem lintegral_normalized_restricted_allocation_ae_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Measure X) (a : Ω → X → Fin (m + 1) → ℝ)
    {H : Set X} (hH : MeasurableSet H)
    (energy : Ω → X × Fin (m + 1) → ℝ≥0∞) :
    (∫⁻ w, ∫⁻ e, energy w e
      ∂semidiscreteAllocationMeasure (normalizedFiniteLaw (μ.restrict H)) (a w) ∂P) ≤
      (((μ.restrict H).real univ)⁻¹.toNNReal : ℝ≥0∞) *
        ∫⁻ w, ∫⁻ e, energy w e ∂semidiscreteAllocationMeasure μ (a w) ∂P := by
  calc
    _ ≤ ∫⁻ w, (((μ.restrict H).real univ)⁻¹.toNNReal : ℝ≥0∞) *
        ∫⁻ e, energy w e ∂semidiscreteAllocationMeasure μ (a w) ∂P :=
      lintegral_mono fun w ↦ lintegral_normalized_restricted_allocation_le μ (a w) hH _
    _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top

end Restriction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationHaarPressureCore

/-- A global physical allocation produces its actual cell scene allocation,
with the exact restricted masses and the same reconstructed coefficients. -/
theorem sceneAllocation_of_global
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots)
    {n : ℕ} {p : Fin (n + 1) → ℝ} {allocation : M → Fin (n + 1) → ℝ}
    (halloc : IsSemidiscreteAllocation η₀ p allocation) :
    IsSemidiscreteAllocation (D.sceneLaw η₀ i L)
      (restrictedAllocationMass η₀ (a ⁻¹' L) allocation)
      (fun s ↦ allocation
        (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s)) :=
  semidiscreteAllocation_comp_of_map (measurable_populationSeedPhysicalMap _)
    (D.sceneLaw_physical_recovery hF hcomplete hu ha hinj horder hb hinv
      hη₀reg hη₁reg i hL hsub).1
    (semidiscreteAllocation_normalized_restrict halloc (a ⁻¹' L))

end PopulationHaarPressureCore
end OTSelector.Reconstruction
