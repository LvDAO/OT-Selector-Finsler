import OTSelector.Geometry.FinslerDistanceLocalizationPhysical

/-!
# The retained physical distance cores are the actual compact seed images

The original root-clock inverse identifies each retained physical core with the
image of its already produced compact seed domain. These are pairwise disjoint
compact sets; their finite union can serve as the same physical core in sampling
and marginal-mass restriction arguments.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Function OTSelector.Geometry
open scoped ENNReal
namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)

/-- The original physical core is precisely the actual image of the retained
compact root and time domain, without any extra reconstruction choice. -/
theorem physicalCoreDomain_eq_image (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) :
    D.physicalCoreDomain i = D.corePoint i '' D.corePointDomain i := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨(a x, u x), hx.2,
      D.corePoint_eq_of_mem_physicalCoreDomain hF hcomplete hu ha hinj horder i hx⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hreg, hroot⟩ := D.corePoint_root_data hF hcomplete hu ha hinj horder i hz
    have ht := (D.corePoint_seed_data hF hcomplete hu ha hinj i hz).2
    have hclock : u (D.corePoint i z) = z.2 := by
      have hh := interior_subset ht
      change u (D.corePoint i z) =
        ((P (D.haar.continuous.coefficient i).seedIndex).seed.level : ℝ) +
          (z.2 - (P (D.haar.continuous.coefficient i).seedIndex).seed.level) at hh
      simpa only [add_sub_cancel] using hh
    exact ⟨hreg, by simpa only [hroot, hclock, Prod.eta] using hz⟩

/-- Every retained original physical core is compact. -/
theorem isCompact_physicalCoreDomain (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) : IsCompact (D.physicalCoreDomain i) := by
  rw [D.physicalCoreDomain_eq_image hF hcomplete hu ha hinj horder i]
  exact (D.isCompact_corePointDomain i).image_of_continuousOn (D.continuousOn_corePoint i)

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M] in
/-- Distinct retained original root pieces also give disjoint physical cores. -/
theorem pairwise_disjoint_physicalCoreDomain : Pairwise
    (fun i j : Fin D.haar.continuous.count ↦ Disjoint (D.physicalCoreDomain i) (D.physicalCoreDomain j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (D.haar.continuous.disjoint hij) hx.2.1 hy.2.1

/-- The entire retained physical core remains compact under the same finite
piece union used in the original population recovery. -/
theorem isCompact_iUnion_physicalCoreDomain (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    IsCompact (⋃ i : Fin D.haar.continuous.count, D.physicalCoreDomain i) :=
  isCompact_iUnion (fun i ↦ D.isCompact_physicalCoreDomain hF hcomplete hu ha hinj horder i)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
