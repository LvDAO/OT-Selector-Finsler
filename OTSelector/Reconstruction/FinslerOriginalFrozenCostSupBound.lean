import OTSelector.Reconstruction.FinslerFrozenCoreDomination
import OTSelector.Reconstruction.FinslerTileBlockFrozenComparison

/-!
# Frozen physical cost sup bound and base probe bound

This module closes the two remaining inputs of
FinslerOriginalTileNormalization.lean: the uniform frozen physical cost bound
phys <= B and the base probe sup bound |base| <= Bp.

## The frozen physical cost sup bound

The Taylor relative bound TaylorRootCover.frozenPhysicalCost_le_slack_of_relative
gives (1 - 2 eps) * phys <= lengthEDist x y - u y + u x on a retained edge.  Since
the Finsler length between the sample points is bounded by Dm and the potential is
bounded by U in absolute value on the sample points, the right side is at most
Dm + 2 U, hence

  phys <= (Dm + 2 U) / (1 - 2 eps)

provided 0 <= eps and 2 eps < 1.  Nonnegativity of phys on retained edges is the
existing frozenPhysicalCost_nonneg, so the two-sided bound |phys| <= B holds with
B = (Dm + 2 U) / (1 - 2 eps) (which is nonnegative).

## The base probe sup bound

The base probe matrix is the evaluation of a bounded continuous probe function
probe : (M x M) ->b R on the sample pairs; its entries are bounded by the norm
norm probe, so Bp = norm probe.  This is the concrete instantiation of the
abstract base matrix.

## Contents

* frozenPhysicalCost_le_of_boundedEdge: the pointwise upper bound with explicit
  B = (Dm + 2 U) / (1 - 2 eps).
* frozenPhysicalCost_abs_le_of_boundedEdge: the two-sided bound.
* exists_frozenPhysicalCost_uniformSupBound: the uniform bound
  exists B, forall n c s i j, phys (ref c) (X n i s) (Y n j s) <= B, i.e. exactly
  hypothesis (a) of FinslerOriginalTileNormalization.lean.
* probeMatrixBase, abs_probeMatrixBase_le: the concrete base probe matrix and its
  sup bound norm probe, i.e. hypothesis |base| <= Bp.

## Exact remaining gap

The geometric side conditions of the retained edge (the reference root in the
cover centers, the root and neighborhood memberships, the window membership and
the two exact-readout equations) and the numeric bounds Dm on the Finsler length
and U on the potential on the sample points: these are the natural boundedness
hypotheses on the real sample, not normalization facts.  Once they hold, both
inputs of the normalized tile lane are discharged.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators
open BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- **Pointwise frozen physical cost upper bound.**  On a retained edge, with the
Finsler length bounded by Dm and the potential bounded by U, the frozen physical
cost is at most (Dm + 2 U)/(1 - 2 eps). -/
theorem frozenPhysicalCost_le_of_boundedEdge
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u => (a x.val, u x.val)))
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    {z₀ : Z} {x y : M}
    (hz₀ : z₀ ∈ D.centers)
    (hx : a x ∈ C.roots ∩ D.neighborhood z₀)
    (hy : a y ∈ C.roots ∩ D.neighborhood z₀)
    (hp : (u x, u y) ∈ C.window.region)
    (hxread : x = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a x))
      (u x - (P C.seedIndex).seed.level))
    (hyread : y = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a y))
      (u y - (P C.seedIndex).seed.level))
    {Dm U : ℝ} (hd : (F.lengthEDist x y).toReal ≤ Dm)
    (hux : |u x| ≤ U) (huy : |u y| ≤ U) :
    C.frozenPhysicalCost z₀ x y ≤ (Dm + 2 * U) / (1 - 2 * ε) := by
  have hslack := D.frozenPhysicalCost_le_slack_of_relative hF hcomplete hu ha hinj
    hε hε1 hz₀ hx hy hp hxread hyread
  have hpos : (0 : ℝ) < 1 - 2 * ε := by linarith
  have hbound : (1 - 2 * ε) * C.frozenPhysicalCost z₀ x y ≤ Dm + 2 * U := by
    have h1 : -u y ≤ |u y| := neg_le_abs (u y)
    have h2 : u x ≤ |u x| := le_abs_self (u x)
    linarith
  refine (le_div_iff₀ hpos).mpr ?_
  calc C.frozenPhysicalCost z₀ x y * (1 - 2 * ε)
      = (1 - 2 * ε) * C.frozenPhysicalCost z₀ x y := by ring
    _ ≤ Dm + 2 * U := hbound

/-- **Two-sided frozen physical cost bound.**  Nonnegativity on a retained edge
(the positive definite frozen coefficient) plus the upper bound gives
|phys| <= (Dm + 2 U)/(1 - 2 eps). -/
theorem frozenPhysicalCost_abs_le_of_boundedEdge
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u => (a x.val, u x.val)))
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    {z₀ : Z} {x y : M}
    (hz₀ : z₀ ∈ D.centers)
    (hx : a x ∈ C.roots ∩ D.neighborhood z₀)
    (hy : a y ∈ C.roots ∩ D.neighborhood z₀)
    (hp : (u x, u y) ∈ C.window.region)
    (hxread : x = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a x))
      (u x - (P C.seedIndex).seed.level))
    (hyread : y = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a y))
      (u y - (P C.seedIndex).seed.level))
    {Dm U : ℝ} (hd : (F.lengthEDist x y).toReal ≤ Dm)
    (hux : |u x| ≤ U) (huy : |u y| ≤ U) :
    |C.frozenPhysicalCost z₀ x y| ≤ (Dm + 2 * U) / (1 - 2 * ε) := by
  have hnonneg : 0 ≤ C.frozenPhysicalCost z₀ x y :=
    frozenPhysicalCost_nonneg D hz₀ hp
  have hupper : C.frozenPhysicalCost z₀ x y ≤ (Dm + 2 * U) / (1 - 2 * ε) :=
    frozenPhysicalCost_le_of_boundedEdge hF hcomplete hu ha hinj D hε hε1 hz₀ hx hy hp
      hxread hyread hd hux huy
  rw [abs_of_nonneg hnonneg]
  exact hupper

/-- **Uniform frozen physical cost sup bound.**  If every sample edge is a retained
edge of a cover (reference root in the centers, root and neighborhood memberships,
window membership and exact readouts), with the Finsler length bounded by Dm and
the potential bounded by U, then there is a single constant B bounding all frozen
physical costs — exactly hypothesis (a) of the normalized tile lane. -/
theorem exists_frozenPhysicalCost_uniformSupBound
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u => (a x.val, u x.val)))
    {ι : Type*} {C : ι → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ}
    {ε : ℝ} (D : ∀ c, (C c).TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    {Ω : ℕ → Type*} (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (ref : ι → Z) {Dm U : ℝ}
    (hz₀ : ∀ c, ref c ∈ (D c).centers)
    (hx : ∀ (n : ℕ) (c : ι) (s : Ω n) (i : Fin (n + 1)),
      a (X n i s) ∈ (C c).roots ∩ (D c).neighborhood (ref c))
    (hy : ∀ (n : ℕ) (c : ι) (s : Ω n) (j : Fin (n + 1)),
      a (Y n j s) ∈ (C c).roots ∩ (D c).neighborhood (ref c))
    (hp : ∀ (n : ℕ) (c : ι) (s : Ω n) (i j : Fin (n + 1)),
      (u (X n i s), u (Y n j s)) ∈ (C c).window.region)
    (hxread : ∀ (n : ℕ) (c : ι) (s : Ω n) (i : Fin (n + 1)),
      X n i s = (P (C c).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (C c).seedIndex).seed a (a (X n i s)))
        (u (X n i s) - (P (C c).seedIndex).seed.level))
    (hyread : ∀ (n : ℕ) (c : ι) (s : Ω n) (j : Fin (n + 1)),
      Y n j s = (P (C c).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (C c).seedIndex).seed a (a (Y n j s)))
        (u (Y n j s) - (P (C c).seedIndex).seed.level))
    (hd : ∀ (n : ℕ) (c : ι) (s : Ω n) (i j : Fin (n + 1)),
      (F.lengthEDist (X n i s) (Y n j s)).toReal ≤ Dm)
    (hux : ∀ (n : ℕ) (c : ι) (s : Ω n) (i : Fin (n + 1)), |u (X n i s)| ≤ U)
    (huy : ∀ (n : ℕ) (c : ι) (s : Ω n) (j : Fin (n + 1)), |u (Y n j s)| ≤ U) :
    ∃ B : ℝ, ∀ (n : ℕ) (c : ι) (s : Ω n) (i j : Fin (n + 1)),
      (C c).frozenPhysicalCost (ref c) (X n i s) (Y n j s) ≤ B :=
  ⟨(Dm + 2 * U) / (1 - 2 * ε), fun n c s i j ↦
    frozenPhysicalCost_le_of_boundedEdge hF hcomplete hu ha hinj (D c) hε hε1
      (hz₀ c) (hx n c s i) (hy n c s j) (hp n c s i j) (hxread n c s i)
      (hyread n c s j) (hd n c s i j) (hux n c s i) (huy n c s j)⟩

/-- The concrete base probe matrix: entries are the probe readout on the sample
pair (X n i s, Y n j s), the sample points lying in the probe domain K. -/
noncomputable def probeMatrixBase {Ω : ℕ → Type*} {ι : Type*} {K : Set M}
    (probe : (K × K) →ᵇ ℝ) (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K) :
    ∀ n, Ω n → ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun n s _ i j ↦ probe (⟨X n i s, hX n i s⟩, ⟨Y n j s, hY n j s⟩)

/-- **Base probe sup bound.**  For the concrete base probe matrix given by a
bounded continuous probe readout, all entries are bounded by norm probe. -/
theorem abs_probeMatrixBase_le {Ω : ℕ → Type*} {ι : Type*} {K : Set M}
    (probe : (K × K) →ᵇ ℝ) (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)) (s : Ω n), X n i s ∈ K)
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)) (s : Ω n), Y n j s ∈ K)
    (n : ℕ) (s : Ω n) (c : ι) (i j : Fin (n + 1)) :
    |probeMatrixBase (Ω := Ω) (ι := ι) probe X Y hX hY n s c i j| ≤ ‖probe‖ := by
  show |probe (⟨X n i s, hX n i s⟩, ⟨Y n j s, hY n j s⟩)| ≤ ‖probe‖
  simpa only [Real.norm_eq_abs] using
    BoundedContinuousFunction.norm_coe_le_norm probe
      (⟨X n i s, hX n i s⟩, ⟨Y n j s, hY n j s⟩)

end OTSelector.Reconstruction