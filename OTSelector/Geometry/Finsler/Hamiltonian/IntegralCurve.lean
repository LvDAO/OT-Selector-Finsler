import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Lemma skeleton

* **Conditions:** A C1 autonomous field for local uniqueness and a smooth field on an open domain for existence; finite-dimensional positive fiber Hessian for the final energy constructor.
* **Objects:** Integral-curve germs and constructed local Hamiltonian curves.
* **Proof detail:** Apply Picard–Lindelöf, restrict trajectories to the open domain, bootstrap smoothness, and combine with the constructed Legendre chart.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249

**Relationship to the sources:** The general existence/uniqueness parts use complete normed spaces where stated. The final regular-Lagrangian wrapper supplies the inverse and field rather than assuming them.
-/

/-!
# Local integral curves of the Hamiltonian field

A smooth autonomous field on an open subset of a real Banach space has a smooth local
integral curve that remains in that subset. Local Lipschitz continuity proves uniqueness
of the solution germ, and differentiating the ODE upgrades the curve to smoothness in time.

For a finite-dimensional scalar energy with positive actual vertical Hessian, the final
theorem constructs the joint Legendre inverse, its Hamiltonian field, and these curves from
the energy hypotheses. It assumes neither an inverse nor an ODE solution. The result is
local in time and makes no assertion of joint smooth dependence on the initial point.
-/

open Set Filter Metric
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuously differentiable autonomous field has uniqueness of integral-curve germs.
No separate assumption that the competing curves stay in a Lipschitz region is needed. -/
theorem integralCurve_eventuallyEq_of_contDiffAt
    {X : F → F} {p : F} (hX : ContDiffAt ℝ 1 X p)
    {α β : ℝ → F} {t₀ : ℝ} (hα₀ : α t₀ = p) (hβ₀ : β t₀ = p)
    (hα : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (X (α t)) t)
    (hβ : ∀ᶠ t in 𝓝 t₀, HasDerivAt β (X (β t)) t) : α =ᶠ[𝓝 t₀] β := by
  obtain ⟨K, s, hs, hlip⟩ := hX.exists_lipschitzOnWith
  have hαc : ContinuousAt α t₀ := (hα.self_of_nhds).continuousAt
  have hβc : ContinuousAt β t₀ := (hβ.self_of_nhds).continuousAt
  have hαs : ∀ᶠ t in 𝓝 t₀, α t ∈ s :=
    hαc.preimage_mem_nhds (by simpa [hα₀] using hs)
  have hβs : ∀ᶠ t in 𝓝 t₀, β t ∈ s :=
    hβc.preimage_mem_nhds (by simpa [hβ₀] using hs)
  exact ODE_solution_unique_of_eventually (v := fun _ ↦ X) (s := fun _ ↦ s)
    (Eventually.of_forall fun _ ↦ hlip) (hα.and hαs) (hβ.and hβs)
    (hα₀.trans hβ₀.symm)

/-- An autonomous field smooth on an open set has a local curve which stays in that set. -/
theorem exists_integralCurve_in_open [CompleteSpace F]
    {X : F → F} {U : Set F} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {p : F} (hp : p ∈ U) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → F, α t₀ = p ∧
      MapsTo α (Ioo (t₀ - ε) (t₀ + ε)) U ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (X (α t)) t := by
  have hXp : ContDiffAt ℝ 1 X p := (hX.contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  obtain ⟨α, hα₀, ε, hε, hα⟩ :=
    hXp.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hstay : ∀ᶠ t in 𝓝 t₀, α t ∈ U :=
    (hα t₀ ht₀).continuousAt.preimage_mem_nhds (by simpa [hα₀] using hU.mem_nhds hp)
  obtain ⟨δ, hδ, hδstay⟩ := Metric.eventually_nhds_iff_ball.mp hstay
  refine ⟨min ε δ, lt_min hε hδ, α, hα₀, ?_, ?_⟩
  · intro t ht
    apply hδstay
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith [min_le_right ε δ, ht.1, ht.2]
  · intro t ht
    apply hα t
    constructor <;> linarith [min_le_left ε δ, ht.1, ht.2]

/-- An integral curve of a smooth autonomous vector field is smooth in time. -/
theorem contDiffOn_integralCurve_of_isOpen
    {V : F → F} {U : Set F} {s : Set ℝ} {γ : ℝ → F}
    (hV : ContDiffOn ℝ ∞ V U) (hs : IsOpen s) (hmap : MapsTo γ s U)
    (hγ : ∀ t ∈ s, HasDerivAt γ (V (γ t)) t) :
    ContDiffOn ℝ ∞ γ s := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun t ht ↦ (hγ t ht).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun t ht ↦ (hγ t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    apply ((contDiffOn_infty.mp hV n).comp ih hmap).congr
    intro t ht
    exact (hγ t ht).deriv

/-- Local existence, smoothness in time, and uniqueness of the integral-curve germ. -/
theorem exists_smooth_integralCurve_in_open [CompleteSpace F]
    {X : F → F} {U : Set F} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {p : F} (hp : p ∈ U) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → F, α t₀ = p ∧
      MapsTo α (Ioo (t₀ - ε) (t₀ + ε)) U ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (X (α t)) t) ∧
      ContDiffOn ℝ ∞ α (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ β : ℝ → F, β t₀ = p →
        (∀ᶠ t in 𝓝 t₀, HasDerivAt β (X (β t)) t) → β =ᶠ[𝓝 t₀] α := by
  obtain ⟨ε, hε, α, hα₀, hmap, hα⟩ := exists_integralCurve_in_open hU hX hp t₀
  refine ⟨ε, hε, α, hα₀, hmap, hα,
    contDiffOn_integralCurve_of_isOpen hX isOpen_Ioo hmap hα, ?_⟩
  intro β hβ₀ hβ
  have hαevent : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (X (α t)) t :=
    Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hα
  exact integralCurve_eventuallyEq_of_contDiffAt
    ((hX.contDiffAt (hU.mem_nhds hp)).of_le (by simp)) hβ₀ hα₀ hβ hαevent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual local Hamiltonian field has a smooth integral curve at every point of
its inverse chart target. The solution germ is unique. -/
theorem exists_localHamiltonian_integralCurve [CompleteSpace E]
    {L : E × E → ℝ}
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E × (E →L[ℝ] ℝ), α t₀ = p ∧
      MapsTo α (Ioo (t₀ - ε) (t₀ + ε)) e.target ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt α (localHamiltonianVectorField L e (α t)) t) ∧
      ContDiffOn ℝ ∞ α (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ β : ℝ → E × (E →L[ℝ] ℝ), β t₀ = p →
        (∀ᶠ t in 𝓝 t₀, HasDerivAt β (localHamiltonianVectorField L e (β t)) t) →
        β =ᶠ[𝓝 t₀] α :=
  exists_smooth_integralCurve_in_open e.open_target
    (contDiffOn_localHamiltonianVectorField hL hG) hp t₀

/-- A smooth scalar energy with positive actual vertical Hessian produces its own
local Hamiltonian chart, field, and smooth integral curves through every target point.
Uniqueness is equality of solution germs at the specified initial time. -/
theorem exists_hamiltonian_integralCurve [FiniteDimensional ℝ E]
    {L : E × E → ℝ} {U : Set (E × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U)
    (hpos : ∀ z ∈ U, ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w)
    {z : E × E} (hz : z ∈ U) (t₀ : ℝ) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ parametricLegendre L z ∈ e.target ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonian L e) e.target ∧
      ContDiffOn ℝ ∞ (localHamiltonianVectorField L e) e.target ∧
      (∀ p ∈ e.target, ∀ dq : E × (E →L[ℝ] ℝ),
        fderiv ℝ (localHamiltonian L e) p dq =
          dq.2 (localHamiltonianVectorField L e p).1 -
            (localHamiltonianVectorField L e p).2 dq.1) ∧
      ∀ p ∈ e.target,
        ∃ ε > (0 : ℝ), ∃ α : ℝ → E × (E →L[ℝ] ℝ), α t₀ = p ∧
          MapsTo α (Ioo (t₀ - ε) (t₀ + ε)) e.target ∧
          (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
            HasDerivAt α (localHamiltonianVectorField L e (α t)) t) ∧
          ContDiffOn ℝ ∞ α (Ioo (t₀ - ε) (t₀ + ε)) ∧
          ∀ β : ℝ → E × (E →L[ℝ] ℝ), β t₀ = p →
            (∀ᶠ t in 𝓝 t₀, HasDerivAt β (localHamiltonianVectorField L e (β t)) t) →
            β =ᶠ[𝓝 t₀] α := by
  obtain ⟨e, he, hzsource, htarget, hsource, hinverse, hH, hX, hidentity⟩ :=
    exists_smooth_localHamiltonian hU hL hpos hz
  exact ⟨e, he, hzsource, htarget, hsource, hinverse, hH, hX, hidentity,
    fun _ hp ↦ exists_smooth_integralCurve_in_open e.open_target hX hp t₀⟩

end OTSelector.Geometry
