import OTSelector.Reconstruction.FinslerOriginalStationaryClassContinuity
import OTSelector.Reconstruction.MarkedStationaryValueLegalFiniteMomentReserve

/-!
# Uniform coefficient/probe convergence from regularity, and the finite-moment reserve

`FinslerOriginalStationaryClassContinuity` reduces the local pressure continuity of
the forward stationary pressure family to two input hypotheses:

* `hA_conv`: eventual uniform closeness of the calibrated coefficient family
  `A j z` as the root `z` tends to `z₀`, and
* `hf_conv`: eventual uniform closeness of the probe family `f j z`.

This file derives them from coefficient/probe regularity:

* `eventually_forall_abs_apply_sub_le_of_continuousAt`: a general compactness
  reduction.  If a two-variable amplitude `F : X → Y → ℝ` is jointly continuous
  at every point of the slice `{x₀} × S` with `S` compact, then eventually in `x`
  every `s ∈ S` satisfies `|F x s - F x₀ s| ≤ ε`.  No uniform structure on `X`
  is needed: a finite subcover of the compact window and a finite intersection of
  root neighborhoods give the bound.
* `hA_conv_on_compact_window` / `hf_conv_on_compact_sample`: the coefficient and
  probe forms of the reduction on a compact height window (respectively a compact
  marked-pair sample).  These are the uniform convergence inputs of the
  stationary-class continuity, restricted to the physical window on which the
  calibrated coefficient and the probe are evaluated.
* `stationaryForward_rootIndependent_hclass_hconv`: for a root-independent
  (frozen) coefficient and probe the refinement hypotheses hold outright, with
  exact zero energy error: this is the formal content of probe freezing in the
  stationary-class reduction.
* `exists_legalReserve_finiteSecondMoment`: the existing finite-second-moment
  reserve is nonempty in the legal stationary Poisson class, instantiated at the
  zero probe.

The remaining gap is that the forward stationary families are stated with global
quantifiers over all real heights and all marked points, while regularity only
delivers uniform closeness on the compact physical window; and the concrete
finite-second-moment reserve lives in the legal Poisson pipeline, for which no
bridge to the abstract `StationaryForwardMatching` carrier exists in the library.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
  Matrix Module Manifold OTSelector.PointProcess OTSelector.Geometry
  ContinuousFinslerNorm OTSelector.Probability
open scoped Topology ContDiff BigOperators Matrix.Norms.Operator

noncomputable section

namespace OTSelector.Reconstruction

/-! ## Compact-window uniform convergence from joint continuity -/

/-- Compactness reduction: if the amplitude `F : X → Y → ℝ` is jointly
continuous at every point of the slice `{x₀} × S` with `S` compact, then
eventually in `x` the values at `x` and `x₀` are uniformly close on `S`. -/
theorem eventually_forall_abs_apply_sub_le_of_continuousAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set Y} (hS : IsCompact S) (F : X → Y → ℝ) {x₀ : X}
    (hcont : ∀ s ∈ S, ContinuousAt (fun p : X × Y ↦ F p.1 p.2) (x₀, s))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ s ∈ S, |F x s - F x₀ s| ≤ ε := by
  have hε2 : 0 < ε / 2 := by linarith
  have hchoice : ∀ s : S, ∃ (U : Set X) (V : Set Y),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ (s : Y) ∈ V ∧
      ∀ (x : X) (y : Y), x ∈ U → y ∈ V → |F x y - F x₀ (s : Y)| < ε / 2 := by
    intro s
    have hΦ : ContinuousAt (fun p : X × Y ↦ F p.1 p.2) (x₀, (s : Y)) := hcont s s.2
    have hball : Set.Ioo (F x₀ (s : Y) - ε / 2) (F x₀ (s : Y) + ε / 2) ∈
        𝓝 (F x₀ (s : Y)) :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hmem : {p : X × Y | F p.1 p.2 ∈
        Set.Ioo (F x₀ (s : Y) - ε / 2) (F x₀ (s : Y) + ε / 2)} ∈
        𝓝 (x₀, (s : Y)) :=
      (show Tendsto (fun p : X × Y ↦ F p.1 p.2) (𝓝 (x₀, (s : Y)))
        (𝓝 (F x₀ (s : Y))) from hΦ).eventually hball
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hmem
    refine ⟨interior u, interior v, isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hu, isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hv, fun x y hx hy ↦ ?_⟩
    have hmem' := huv (show (x, y) ∈ u ×ˢ v from
      ⟨interior_subset hx, interior_subset hy⟩)
    rw [abs_lt]
    constructor <;> linarith [hmem'.1, hmem'.2]
  choose U V hUopen hxU hVopen hsV hbound using hchoice
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : S ↦ V s)
    (fun s ↦ hVopen s) (fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hsV ⟨y, hy⟩⟩)
  have hWopen : IsOpen (⋂ s ∈ t, U s) :=
    isOpen_biInter_finset (fun s _ ↦ hUopen s)
  have hxW : x₀ ∈ ⋂ s ∈ t, U s := by
    simp only [Set.mem_iInter]
    exact fun s _ ↦ hxU s
  filter_upwards [hWopen.mem_nhds hxW] with z hz s hs
  obtain ⟨s₀, hs₀t, hys₀⟩ := Set.mem_iUnion₂.mp (ht hs)
  have hzU : z ∈ U s₀ := by
    have h := hz
    simp only [Set.mem_iInter] at h
    exact h s₀ hs₀t
  have h1 : |F z s - F x₀ (s₀ : Y)| < ε / 2 := hbound s₀ z s hzU hys₀
  have h2 : |F x₀ s - F x₀ (s₀ : Y)| < ε / 2 := hbound s₀ x₀ s (hxU s₀) hys₀
  have htri : |F z s - F x₀ s| ≤
      |F z s - F x₀ (s₀ : Y)| + |F x₀ (s₀ : Y) - F x₀ s| := by
    calc |F z s - F x₀ s|
        = |(F z s - F x₀ (s₀ : Y)) + (F x₀ (s₀ : Y) - F x₀ s)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hsym : |F x₀ (s₀ : Y) - F x₀ s| = |F x₀ s - F x₀ (s₀ : Y)| :=
    abs_sub_comm _ _
  linarith [htri, h1, h2, abs_nonneg (F x₀ (s₀ : Y) - F x₀ s)]

/-- Coefficient form of the compactness reduction on a compact height window
`S ⊆ ℝ × ℝ`: joint continuity of `(z, a, b) ↦ A j z a b` at the slice
`{z₀} × S` gives eventual uniform convergence of the coefficient on the window. -/
theorem hA_conv_on_compact_window
    {Z : Type*} [TopologicalSpace Z] {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (A : ℕ → Z → ℝ → ℝ → ℝ) (j : ℕ) {z₀ : Z}
    (hcont : ∀ s ∈ S,
      ContinuousAt (fun p : Z × (ℝ × ℝ) ↦ A j p.1 p.2.1 p.2.2) (z₀, s)) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ s ∈ S,
      |A j z s.1 s.2 - A j z₀ s.1 s.2| ≤ ε := by
  intro ε hε
  exact eventually_forall_abs_apply_sub_le_of_continuousAt hS
    (fun z (s : ℝ × ℝ) ↦ A j z s.1 s.2) hcont hε

/-- Probe form of the compactness reduction on a compact marked-pair sample
`T ⊆ MarkedCloudPoint × MarkedCloudPoint`. -/
theorem hf_conv_on_compact_sample
    {Z : Type*} [TopologicalSpace Z]
    {T : Set (MarkedCloudPoint × MarkedCloudPoint)} (hT : IsCompact T)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ) (j : ℕ) {z₀ : Z}
    (hcont : ∀ q ∈ T, ContinuousAt
      (fun p : Z × (MarkedCloudPoint × MarkedCloudPoint) ↦
        f j p.1 p.2.1 p.2.2) (z₀, q)) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ q ∈ T, |f j z q.1 q.2 - f j z₀ q.1 q.2| ≤ ε := by
  intro ε hε
  exact eventually_forall_abs_apply_sub_le_of_continuousAt hT
    (fun z (q : MarkedCloudPoint × MarkedCloudPoint) ↦ f j z q.1 q.2) hcont hε

end OTSelector.Reconstruction

/-! ## The frozen (root-independent) coefficient/probe case -/

namespace OTSelector.PointProcess

open StationaryForwardMatching

variable {α β : Measure UnitMark}

/-- For a root-independent (frozen) calibrated coefficient and probe, the two
refinement hypotheses hold outright with zero energy error: the stationary class
and both Palm energies do not depend on the root. -/
theorem stationaryForward_rootIndependent_hclass_hconv
    {Z : Type*} [TopologicalSpace Z]
    (A : ℕ → ℝ → ℝ → ℝ) (f : ℕ → MarkedCloudPoint → MarkedCloudPoint → ℝ) :
    (∀ (j : ℕ) (z₀ : Z), ∀ᶠ z in 𝓝 z₀,
        stationaryForwardWeightedClass α β (fun j _ ↦ A j) j z =
          stationaryForwardWeightedClass α β (fun j _ ↦ A j) j z₀) ∧
      (∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
        ∀ w ∈ stationaryForwardWeightedClass α β (fun j _ ↦ A j) j z₀,
          |stationaryForwardKineticFamily α β (fun j _ ↦ A j) j z w -
            stationaryForwardKineticFamily α β (fun j _ ↦ A j) j z₀ w| ≤ ε ∧
          |stationaryForwardProbeFamily α β (fun j _ ↦ f j) j z w -
            stationaryForwardProbeFamily α β (fun j _ ↦ f j) j z₀ w| ≤ ε) := by
  refine ⟨fun j z₀ ↦ ?_, fun j z₀ ε hε ↦ ?_⟩
  · filter_upwards with z
    rfl
  · filter_upwards with z
    intro w _
    constructor
    · simp only [stationaryForwardKineticFamily, sub_self, abs_zero]
      exact hε.le
    · simp only [stationaryForwardProbeFamily, sub_self, abs_zero]
      exact hε.le

end OTSelector.PointProcess

/-! ## Nonemptiness of the finite-second-moment reserve -/

namespace OTSelector.Reconstruction

/-- The existing finite-second-moment reserve, instantiated at the zero probe:
the legal stationary Poisson class contains a matching with finite displacement
second moment. -/
theorem exists_legalReserve_finiteSecondMoment
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {F : ContinuousFinslerNorm E M} {u : M → ℝ}
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) :
    ∃ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) (fun _ _ ↦ (0 : ℝ)),
      Integrable (fun m ↦ ‖m.2‖ ^ 2)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
  D.exists_original_focal_finiteSecondMoment_stationaryMatching hF hw hq hgap
    hbounds π hπ horder (G := 0) (g := fun _ _ ↦ 0) measurable_const
    (fun _ _ ↦ by simp)

end OTSelector.Reconstruction

end
