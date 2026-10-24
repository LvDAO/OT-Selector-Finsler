import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ManifoldFlowTimePotential.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ManifoldFlowTimePotential`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual inverse tube and the specified momentum pairing for its forward differential.

Objects: Flow-time potential and its actual differential, including the derivative along the flow.

Proof detail: Take the inverse first coordinate and differentiate the inverse identity; evaluate the pairing on forward variations and the time direction.

Sources: Gerald Teschl, Section 6.2, Lemma 6.2 and proof, pp. 190–191 (straightening out of vector fields) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=201); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: A flow-box potential construction with explicit momentum assumptions; not a claim that an arbitrary flow is calibrated.
-/

/-!
# The intrinsic time potential of a manifold tube

The first component of the actual inverse tube map defines one scalar potential on
its whole manifold target. The genuine inverse identity determines its manifold
differential from a forward momentum pairing. No single ambient chart, replacement
coordinate map, inverse differential identity, or surjectivity premise is supplied.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Speed times the first inverse tube coordinate, measured from the given time origin. -/
def manifoldFlowTimePotential (e : OpenPartialHomeomorph (ℝ × W) M)
    (s t₀ : ℝ) (x : M) : ℝ := s * ((e.symm x).1 - t₀)

omit [NormedSpace ℝ W] in
/-- The same original forward tube map recovers its prescribed affine time potential. -/
theorem manifoldFlowTimePotential_apply (e : OpenPartialHomeomorph (ℝ × W) M)
    (s t₀ : ℝ) {q : ℝ × W} (hq : q ∈ e.source) :
    manifoldFlowTimePotential e s t₀ (e q) = s * (q.1 - t₀) := by
  simp only [manifoldFlowTimePotential, e.left_inv hq]

/-- The potential inherits the full manifold regularity of the actual tube inverse. -/
theorem contMDiffOn_manifoldFlowTimePotential (e : OpenPartialHomeomorph (ℝ × W) M)
    {n : ℕ∞ω} (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) n e.symm e.target)
    (s t₀ : ℝ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n (manifoldFlowTimePotential e s t₀) e.target := by
  have hφ : ContDiff ℝ n (fun q : ℝ × W ↦ s * (q.1 - t₀)) :=
    contDiff_const.mul (contDiff_fst.sub contDiff_const)
  exact hφ.contMDiff.comp_contMDiffOn hi

/-- Actual mutual inverses and the forward pairing determine the intrinsic differential
of this concrete potential. The pairing covector lives in the true target tangent space. -/
theorem mfderiv_manifoldFlowTimePotential_of_pairing
    (e : OpenPartialHomeomorph (ℝ × W) M) {q : ℝ × W} (hq : q ∈ e.source)
    (he : MDifferentiableAt 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e q)
    (hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) e.symm (e q))
    (p : TangentSpace 𝓘(ℝ, E) (e q) →L[ℝ] ℝ) {k : ℝ} (hk : k ≠ 0)
    (hpair : ∀ d : ℝ × W, p (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e q d) = k * d.1)
    (s t₀ : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e s t₀) (e q) =
      (s / k) • p := by
  have hleft : e.symm (e q) = q := e.left_inv hq
  have he' : MDifferentiableAt 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e (e.symm (e q)) := by
    simpa only [hleft] using he
  have hid : (e ∘ e.symm) =ᶠ[𝓝 (e q)] (id : M → M) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hq)] with x hx
    exact e.right_inv hx
  have hchain : (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e q).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) e.symm (e q)) =
        ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) (e q)) := by
    have hc := mfderiv_comp (e q) he' hi
    rw [hleft] at hc
    exact hc.symm.trans (hid.mfderiv_eq.trans mfderiv_id)
  have hφ : HasFDerivAt (fun z : ℝ × W ↦ s * (z.1 - t₀))
      (s • ContinuousLinearMap.fst ℝ ℝ W) (e.symm (e q)) := by
    simpa using (hasFDerivAt_fst.sub_const t₀).const_mul s
  have hd := hφ.hasMFDerivAt.comp (e q) hi.hasMFDerivAt
  change HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e s t₀) (e q) _ at hd
  rw [hd.mfderiv]
  ext v
  have hp := hpair (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) e.symm (e q) v)
  have hcv := congrArg
    (fun A : TangentSpace 𝓘(ℝ, E) (e q) →L[ℝ] TangentSpace 𝓘(ℝ, E) (e q) ↦ A v)
    hchain
  change mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) e q
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) e.symm (e q) v) = v at hcv
  rw [hcv] at hp
  change s * (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) e.symm (e q) v).1 = (s / k) * p v
  rw [hp]
  field_simp

omit [NormedSpace ℝ W] in
/-- Along any actual tube time curve the prescribed scalar speed is its true derivative. -/
theorem hasDerivAt_manifoldFlowTimePotential_curve
    (e : OpenPartialHomeomorph (ℝ × W) M) (s t₀ : ℝ)
    {t : ℝ} {w : W} (hq : (t, w) ∈ e.source) :
    HasDerivAt (fun u ↦ manifoldFlowTimePotential e s t₀ (e (u, w))) s t := by
  have heq : (fun u ↦ manifoldFlowTimePotential e s t₀ (e (u, w))) =ᶠ[𝓝 t]
      (fun u ↦ s * (u - t₀)) := by
    have hn : ∀ᶠ u in 𝓝 t, (u, w) ∈ e.source :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
        (e.open_source.mem_nhds hq)
    filter_upwards [hn] with u hu
    exact manifoldFlowTimePotential_apply e s t₀ hu
  have hd : HasDerivAt (fun u : ℝ ↦ s * (u - t₀)) s t := by
    simpa using HasDerivAt.const_mul s ((hasDerivAt_id t).sub_const t₀)
  exact hd.congr_of_eventuallyEq heq

end OTSelector.Geometry

end
end
