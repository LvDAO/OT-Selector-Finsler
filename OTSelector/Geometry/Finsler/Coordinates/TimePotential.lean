import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
## Lemma skeleton

* **Conditions:** An open partial homeomorphism g : H × R → E, differentiable forward and inverse maps where used, and a covector whose pairing with Dg equals a nonzero constant times the time component.
* **Objects:** The concrete scalar inverse time coordinate u(x)=s*((g⁻¹(x)).time-t0); its true differential and derivative along actual coordinate time curves.
* **Proof detail:** Differentiate the actual inverse identity g⁻¹∘g=id. Compose the given forward covector pairing with the resulting inverse derivative, obtaining du=(s/k)p. Evaluate u on g(w,t) to get the time derivative.

## Mathematical sources

* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
  https://www.jirka.org/ra/realanal2.pdf#page=38
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 6.2, Lemma 6.2 and proof, pp. 190–191 (straightening out of vector fields).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=201

**Relationship to the sources:** This is an elementary inverse-chain-rule consequence used in flow-box coordinates. The pairing is a premise of this calculus helper; the Finsler application derives it separately by first variation and Euler homogeneity.
-/

/-!
# The actual time potential of local position coordinates

For a local coordinate homeomorphism with differentiable forward and inverse maps,
construct the scalar time coordinate multiplied by a fixed speed. Differentiating the
actual inverse identity converts a momentum pairing with the forward derivative into
the differential of this concrete potential. No derivative inverse or surjectivity is
supplied as an additional premise. A separate identity gives its derivative along the
actual coordinate time curves.

The momentum pairing remains an input to this calculus lemma; the general Finsler
application derives it from equal-energy first variation and Euler homogeneity.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Speed multiplied by the actual inverse coordinate time relative to a fixed origin. -/
def flowTimePotential (g : OpenPartialHomeomorph (H × ℝ) E) (s t₀ : ℝ) (x : E) : ℝ :=
  s * ((g.symm x).2 - t₀)

omit [NormedSpace ℝ H] [NormedSpace ℝ E] in
/-- The time potential recovers the original time on the coordinate source. -/
theorem flowTimePotential_apply (g : OpenPartialHomeomorph (H × ℝ) E)
    (s t₀ : ℝ) {q : H × ℝ} (hq : q ∈ g.source) :
    flowTimePotential g s t₀ (g q) = s * (q.2 - t₀) := by
  simp only [flowTimePotential, g.left_inv hq]

/-- The actual inverse coordinate regularity is inherited by its time potential. -/
theorem contDiffOn_flowTimePotential (g : OpenPartialHomeomorph (H × ℝ) E)
    {n : WithTop ℕ∞} (hg : ContDiffOn ℝ n g.symm g.target) (s t₀ : ℝ) :
    ContDiffOn ℝ n (flowTimePotential g s t₀) g.target :=
  contDiffOn_const.mul (hg.snd.sub contDiffOn_const)

/-- The true inverse identity identifies the potential differential from forward pairing. -/
theorem fderiv_flowTimePotential_of_pairing
    (g : OpenPartialHomeomorph (H × ℝ) E) {q : H × ℝ} (hq : q ∈ g.source)
    (hg : DifferentiableAt ℝ g q) (hi : DifferentiableAt ℝ g.symm (g q))
    (p : E →L[ℝ] ℝ) {k : ℝ} (hk : k ≠ 0)
    (hpair : ∀ d : H × ℝ, p (fderiv ℝ g q d) = k * d.2) (s t₀ : ℝ) :
    fderiv ℝ (flowTimePotential g s t₀) (g q) = (s / k) • p := by
  have hginv : g.symm (g q) = q := g.left_inv hq
  have hg' : HasFDerivAt (g : H × ℝ → E) (fderiv ℝ g q) (g.symm (g q)) := by
    simpa only [hginv] using hg.hasFDerivAt
  have hc := hg'.comp (g q) hi.hasFDerivAt
  have heq : (fun x ↦ g (g.symm x)) =ᶠ[𝓝 (g q)] (fun x ↦ x) := by
    filter_upwards [g.open_target.mem_nhds (g.map_source hq)] with x hx
    exact g.right_inv hx
  have hchain : (fderiv ℝ g q).comp (fderiv ℝ g.symm (g q)) =
      ContinuousLinearMap.id ℝ E :=
    hc.unique ((hasFDerivAt_id (g q)).congr_of_eventuallyEq heq)
  have hd := (hi.hasFDerivAt.snd.sub_const t₀).const_mul s
  change HasFDerivAt (flowTimePotential g s t₀) _ (g q) at hd
  rw [hd.fderiv]
  ext v
  have hp := hpair (fderiv ℝ g.symm (g q) v)
  have hcv := congrArg (fun A : E →L[ℝ] E ↦ A v) hchain
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hcv
  rw [hcv] at hp
  change s * (fderiv ℝ g.symm (g q) v).2 = (s / k) * p v
  rw [hp]
  field_simp

omit [NormedSpace ℝ H] [NormedSpace ℝ E] in
/-- Along coordinate time curves the potential derivative is the prescribed speed. -/
theorem hasDerivAt_flowTimePotential_curve
    (g : OpenPartialHomeomorph (H × ℝ) E) (s t₀ : ℝ)
    {w : H} {t : ℝ} (ht : (w, t) ∈ g.source) :
    HasDerivAt (fun u ↦ flowTimePotential g s t₀ (g (w, u))) s t := by
  have heq : (fun u ↦ flowTimePotential g s t₀ (g (w, u))) =ᶠ[𝓝 t]
      (fun u ↦ s * (u - t₀)) := by
    have hn : ∀ᶠ u in 𝓝 t, (w, u) ∈ g.source :=
      (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
        (g.open_source.mem_nhds ht)
    filter_upwards [hn] with u hu
    exact flowTimePotential_apply g s t₀ hu
  have hd : HasDerivAt (fun u : ℝ ↦ s * (u - t₀)) s t := by
    simpa using HasDerivAt.const_mul s ((hasDerivAt_id t).sub_const t₀)
  exact hd.congr_of_eventuallyEq heq

end OTSelector.Geometry
