import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartScalarComponentExtensions
import MorganTianLib.Ch01.CurvatureFrameBridge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** chart vector field extension. -/
theorem chart_vector_field_extension {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (W : E3 → E3) (U : Set E3) (hU : IsOpen U) (hxU : x ∈ U)
    (hW : ContDiffOn ℝ ∞ W U) :
    ∃ V : Riemannian.SmoothVectorField (𝓡 3) M,
      ∀ᶠ q : M in 𝓝 ((extChartAt (𝓡 3) a).symm (B x)),
        V q = ∑ k : Fin 3, W (B.symm (extChartAt (𝓡 3) a q)) k •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let φ := extChartAt (𝓡 3) a
  let p : M := φ.symm (B x)
  have hp : p ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) a).source := by
    change φ.symm (B x) ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) a).source
    rw [← Riemannian.extChartAt_source_eq_chartAt_source (I := 𝓡 3)]
    exact φ.map_target hx
  obtain ⟨f, hf, hcoeff⟩ :=
    chart_scalar_component_extensions g a e B hB x hx W U hU hxU hW
  obtain ⟨Z, O, hOopen, hpO, hOsub, hframe, _⟩ :=
    MorganTianLib.exists_chartFrame_leviCivita_christoffel_nhds
      (I := 𝓡 3) g (α := a) hp
  letI : AddCommMonoid (Riemannian.SmoothVectorField (𝓡 3) M) := {
    add_assoc := fun X Y Z => Riemannian.SmoothVectorField.ext fun q =>
      add_assoc (X q) (Y q) (Z q)
    zero_add := fun X => Riemannian.SmoothVectorField.ext fun q => zero_add (X q)
    add_zero := fun X => Riemannian.SmoothVectorField.ext fun q => add_zero (X q)
    add_comm := fun X Y => Riemannian.SmoothVectorField.ext fun q =>
      add_comm (X q) (Y q)
    nsmul := nsmulRec
  }
  have hsum_apply (s : Finset (Fin 3))
      (F : Fin 3 → Riemannian.SmoothVectorField (𝓡 3) M) (q : M) :
      (s.sum F) q = s.sum (fun k => F k q) := by
    classical
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, Riemannian.SmoothVectorField.add_apply, ih]
  refine ⟨∑ k : Fin 3,
    Riemannian.SmoothVectorField.smul (f k) (hf k) (Z (e k)), ?_⟩
  have hframe_eventually : ∀ᶠ q : M in 𝓝 p,
      ∀ k : Fin 3, Z (e k) q =
        Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q := by
    filter_upwards [hOopen.mem_nhds hpO] with q hq
    intro k
    exact hframe (e k) q hq
  filter_upwards [hcoeff, hframe_eventually] with q hqcoeff hqframe
  calc
    (∑ k : Fin 3, Riemannian.SmoothVectorField.smul (f k) (hf k) (Z (e k))) q
        = ∑ k : Fin 3,
          (Riemannian.SmoothVectorField.smul (f k) (hf k) (Z (e k))) q := by
            simpa only using hsum_apply Finset.univ (fun k : Fin 3 =>
              Riemannian.SmoothVectorField.smul (f k) (hf k) (Z (e k))) q
    _ = ∑ k : Fin 3,
        W (B.symm (extChartAt (𝓡 3) a q)) k •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Riemannian.SmoothVectorField.smul_apply]
      rw [hqcoeff k, hqframe k]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
