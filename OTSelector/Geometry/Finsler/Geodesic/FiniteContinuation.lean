import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Geodesic.Proofs.Continuation
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Geodesic.TerminalRechart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFiniteContinuation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFiniteContinuation`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.FiniteContinuation

* **Conditions:** A C2 slit Euler–Lagrange curve on a finite interval and completeness of the original Finsler length metric.
* **Objects:** A right continuation beyond the finite endpoint, smoothly glued to the entire original manifold curve.
* **Proof detail:** Rechart at the constructed terminal position, obtain compact nonzero phase confinement, apply the compact-range continuation principle and glue by local uniqueness.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=63): Section 2.6, Lemma 2.14 and Corollary 2.15, pp. 52–53, including the explicit left-endpoint version.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): The compact-range ODE theorem is used after deriving its phase-confinement hypotheses from Finsler energy and metric completeness.
-/

/-!
# Finite continuation from completeness of the original Finsler metric

An actual C2 slit Euler--Lagrange curve in one chart has a terminal position endpoint
by completeness of the original length metric. Recharting there supplies compact
confinement, so the actual position--velocity equation continues in the endpoint chart.
The new terminal curve glues smoothly to the whole original manifold curve.
-/

open Set Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Completeness of the original length metric continues an actual slit Euler--Lagrange
curve beyond its finite right endpoint, preserving its entire original manifold curve.
The continued curve is smooth, and its actual coordinates in the chart centered at the
endpoint satisfy the slit Euler--Lagrange equation on a terminal interval. -/
theorem exists_finite_chartEulerLagrange_continuation_right (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {x : ℝ → E} {a b : ℝ} (hab : a < b)
    (hx : ContDiffOn ℝ 2 x (Ioo a b))
    (hphase : ∀ t ∈ Ioo a b, (x t, deriv x t) ∈ chartEnergyDomain old)
    (hEL : ∀ t ∈ Ioo a b, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy old) (x s, deriv x s))
      (baseEnergyDifferential (F.chartEnergy old) (x t, deriv x t)) t) :
    ∃ δ > (0 : ℝ), ∃ b₀ ∈ Ioo a b, ∃ new : M, ∃ ηbar : ℝ → E, ∃ cext : ℝ → M,
      EqOn cext ((extChartAt 𝓘(ℝ, E) old).symm ∘ x) (Ioo a b) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ cext (Ioo a (b + δ)) ∧
      cext b = new ∧
      ContDiffOn ℝ ∞ ηbar (Ioo b₀ (b + δ)) ∧
      (∀ t ∈ Ioo b₀ (b + δ), (ηbar t, deriv ηbar t) ∈ chartEnergyDomain new) ∧
      (∀ t ∈ Ioo b₀ (b + δ), HasDerivAt
        (fun s ↦ fiberLegendre (F.chartEnergy new) (ηbar s, deriv ηbar s))
        (baseEnergyDifferential (F.chartEnergy new) (ηbar t, deriv ηbar t)) t) ∧
      EqOn cext ((extChartAt 𝓘(ℝ, E) new).symm ∘ ηbar) (Ioo b₀ (b + δ)) ∧
      EqOn ηbar (chartTransition new old ∘ x) (Ioo b₀ b) := by
  obtain ⟨cbar, hcbar, hcbar_eq, b₀, hb₀, K, hK, hKsub, hη, hηphase,
      hηEL, hηmap, hηeq⟩ :=
    hF.exists_terminal_rechart_eulerLagrange hcomplete old hab hx hphase hEL
  let new := cbar b
  let η := chartTransition new old ∘ x
  obtain ⟨δ, hδ, ηbar, hηbar_eq, hηbar, hηbar_phase, hηbar_EL⟩ :=
    hF.exists_chartEulerLagrange_extension_right new hK hKsub hb₀.2
      (hη.of_le (by simp)) hηmap hηphase hηEL
  let cold := (extChartAt 𝓘(ℝ, E) old).symm ∘ x
  let cnew := (extChartAt 𝓘(ℝ, E) new).symm ∘ ηbar
  let cext : ℝ → M := fun t ↦ if t < b then cold t else cnew t
  have hoverlap : EqOn cnew cold (Ioo b₀ b) := by
    intro t ht
    change (extChartAt 𝓘(ℝ, E) new).symm (ηbar t) = cold t
    rw [hηbar_eq ht]
    exact hηeq ht
  have hold : EqOn cext cold (Ioo a b) := by
    intro t ht
    simp only [cext, ite_eq_left ht.2]
  have hnew : EqOn cext cnew (Ioo b₀ (b + δ)) := by
    intro t ht
    by_cases htb : t < b
    · simpa only [cext, ite_eq_left htb] using (hoverlap ⟨ht.1, htb⟩).symm
    · simp only [cext, ite_eq_right htb]
  have hxSmooth := hF.contDiffOn_chartEulerLagrange_of_contDiffOn_two old
    isOpen_Ioo hx hphase hEL
  have hcold : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ cold (Ioo a b) :=
    (contMDiffOn_extChartAt_symm old).comp hxSmooth.contMDiffOn
      (fun t ht ↦ (hphase t ht).1)
  have hcnew : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ cnew (Ioo b₀ (b + δ)) :=
    (contMDiffOn_extChartAt_symm new).comp hηbar.contMDiffOn
      (fun t ht ↦ (hηbar_phase t ht).1)
  have hcext : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ cext (Ioo a (b + δ)) := by
    apply ((hcold.congr hold).union_of_isOpen (hcnew.congr hnew)
      isOpen_Ioo isOpen_Ioo).mono
    intro t ht
    by_cases htb : t < b
    · exact Or.inl ⟨ht.1, htb⟩
    · exact Or.inr ⟨lt_of_lt_of_le hb₀.2 (le_of_not_gt htb), ht.2⟩
  have hcextCont : ContinuousOn cext (Ioc a b) := hcext.continuousOn.mono (by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 (lt_add_of_pos_right b hδ)⟩)
  have hcbarCont : ContinuousOn cbar (Ioc a b) := hcbar.mono Ioc_subset_Icc_self
  have hcb : EqOn cext cbar (Ioo a b) := by
    intro t ht
    exact (hold ht).trans (hcbar_eq ht).symm
  have hend : cext b = new := by
    apply hcb.of_subset_closure hcextCont hcbarCont Ioo_subset_Ioc_self
      (by rw [closure_Ioo hab.ne]; exact Ioc_subset_Icc_self)
    exact ⟨hab, le_rfl⟩
  exact ⟨δ, hδ, b₀, hb₀, new, ηbar, cext, hold, hcext, hend, hηbar,
    hηbar_phase, hηbar_EL, hnew, hηbar_eq⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
