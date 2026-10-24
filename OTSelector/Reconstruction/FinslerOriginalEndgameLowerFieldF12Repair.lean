import OTSelector.Reconstruction.FinslerOriginalHprobWiring
import OTSelector.Reconstruction.FinslerOriginalEndgameLowerField

/-!
# F12 repair: probe-dependence of the lower pressure field

Audit flag F12 concerns the shifted readout `fun f t ↦ Ψ f t - |t| * ‖f‖` used as the
lower bundle's pressure: the tile-lane hypothesis `hgt : g f t = atlasPiecewiseRoot P a κ
lambda G` has a right-hand side independent of the probe `f` and the tilt `t`, so the
frozen readout `g` is probe-independent; since `frozenPressureLower` only sees `g` through
`g f t` (definitional identity with `campbellAveragedFrozenCost P a κ lambda (g f t) q`),
the readout `Ψ` and hence the shifted pressure are direction-blind in the probe and are
NOT the paper's pressure.

This file (1) proves the artifact, and (2) provides the repaired bundle where the pressure
is the probe-indexed frozen readout itself (unshifted, no `hgt`, no `|t| * ‖f‖` shift):
`endgameLowerFields_actual_lane_f12`.  The genuinely new paper input is isolated as the
named hypothesis `hprobFrozen` (the unshifted probability hprob at the frozen readout).

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open OTSelector.Reconstruction.PopulationLocalPressureCore.TaylorTiles

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

variable {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)

/-- **F12 diagnostic, part 1.**  The tile-lane hypothesis `hgt` makes the frozen
readout `g` probe- and tilt-independent, hence so is `frozenPressureLower g`. -/
theorem frozenPressureLower_probe_independent_of_hgt
    {G : ℕ → (ℚ → M) → ℝ}
    {g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ}
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ)
    (f' : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t' : ℝ) :
    frozenPressureLower P a κ lambda g q f t = frozenPressureLower P a κ lambda g q f' t' := by
  have hg : g f t = g f' t' := (hgt f t).trans (hgt f' t').symm
  calc frozenPressureLower P a κ lambda g q f t
      = campbellAveragedFrozenCost P a κ lambda (g f t) q := rfl
    _ = campbellAveragedFrozenCost P a κ lambda (g f' t') q := by rw [hg]
    _ = frozenPressureLower P a κ lambda g q f' t' := rfl

/-- **F12 diagnostic, part 2.**  With the readout identification `hread` and `hgt`, the
shifted pressure `fun f t ↦ Ψ f t - |t| * ‖f‖` is blind to the probe direction: probes of
equal norm at equal tilts give the same value.  It therefore cannot be the final
consumer's pressure (the paper's pressure varies with the probe). -/
theorem pressureLower_shifted_probe_blind_of_hread
    {G : ℕ → (ℚ → M) → ℝ}
    {g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ}
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    {Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ}
    (hread : frozenPressureLower P a κ lambda g q = Ψ)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ)
    (f' : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t' : ℝ)
    (ht : |t| = |t'|) (hn : (‖f‖₊ : ℝ) = (‖f'‖₊ : ℝ)) :
    Ψ f t - |t| * (‖f‖₊ : ℝ) = Ψ f' t' - |t'| * (‖f'‖₊ : ℝ) := by
  rw [← hread]
  have hfr : frozenPressureLower P a κ lambda g q f t = frozenPressureLower P a κ lambda g q f' t' :=
    frozenPressureLower_probe_independent_of_hgt (G := G) (g := g) hgt f t f' t'
  rw [hfr, ht, hn]

/-- **F12 repair.**  The lower endgame bundle with the paper's probe-indexed unlocked
frozen pressure `fun f t ↦ frozenPressureLower P a κ lambda g q f t`: no `hgt`, no
`|t| * ‖f‖` shift, no probe-independence artifact.  The readout `g` is an arbitrary
(probe-indexed) input.  The remaining genuinely new paper input is isolated as the named
hypothesis `hprobFrozen`: the unshifted probability lower bound at the frozen readout. -/
noncomputable def endgameLowerFields_actual_lane_f12
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (u : M → ℝ)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hprobFrozen : FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u
      (fun f t ↦ frozenPressureLower P a κ lambda g q f t) radius) :
    EndgameLowerFields F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u where
  pressureLower := fun f t ↦ frozenPressureLower P a κ lambda g q f t
  radius := radius
  hradius := hradius
  hprob := hprobFrozen

end OTSelector.Reconstruction
