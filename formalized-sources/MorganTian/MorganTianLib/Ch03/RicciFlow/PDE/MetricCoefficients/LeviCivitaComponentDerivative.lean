import MorganTianLib.Ch01.CurvatureFrameBridge
import DoCarmoLib.Riemannian.Connection.ChartCurvatureMovingPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** levi civita component derivative. -/
theorem levi_civita_component_derivative {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M] (g : Riemannian.RiemannianMetric (𝓡 3) M)
    (a p : M) (hp : p ∈ (chartAt E3 a).source) (e : Fin 3 ≃ Fin (Module.finrank ℝ E3))
    (V : Riemannian.SmoothVectorField (𝓡 3) M) (f : Fin 3 → M → ℝ)
    (hf : ∀ k, ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (f k))
    (hV : ∀ᶠ q : M in 𝓝 p, V q = ∑ k : Fin 3,
      f k q • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q) (i : Fin 3) :
    let df : Fin 3 → ℝ := fun k => mfderiv (𝓡 3) 𝓘(ℝ) (f k) p
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p);
    (g.leviCivitaConnection.cov
      (MorganTianLib.extendVector p (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)) V) p =
      ∑ k : Fin 3, (df k +
        ∑ l : Fin 3, f l p * Riemannian.chartChristoffel g a (e i) (e l) (e k)
          (extChartAt (𝓡 3) a p)) • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp only
  let df : Fin 3 → ℝ := fun k =>
    mfderiv (𝓡 3) 𝓘(ℝ) (f k) p
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
  obtain ⟨X, U, hUopen, hpU, hUsub, hX, hcov⟩ :=
    exists_chartFrame_leviCivita_christoffel_nhds (I := 𝓡 3) g hp
  have hXev : ∀ b, ∀ᶠ q : M in 𝓝 p,
      X b q = Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a b q := by
    intro b
    filter_upwards [hUopen.mem_nhds hpU] with q hq
    exact hX b q hq
  have hdir :
      extendVector p (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p) p
        = X (e i) p := by
    rw [extendVector_apply, (hXev (e i)).self_of_nhds]
  have hloc : ∀ᶠ q : M in 𝓝 p, V q =
      ∑ k ∈ Finset.univ, f k q • X (e k) q := by
    filter_upwards [hV, eventually_all.mpr (fun k : Fin 3 => hXev (e k))]
      with q hq hXq
    calc
      V q = ∑ k : Fin 3, f k q •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q := hq
      _ = ∑ k ∈ Finset.univ, f k q • X (e k) q := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hXq k]
  have hdircoeff (k : Fin 3) : (X (e i)).dir (f k) p = df k := by
    change mfderiv (𝓡 3) 𝓘(ℝ) (f k) p (X (e i) p) =
      mfderiv (𝓡 3) 𝓘(ℝ) (f k) p
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
    rw [(hXev (e i)).self_of_nhds]
  have hframecov (k : Fin 3) :
      (g.leviCivitaConnection.cov (X (e i)) (X (e k))) p =
        ∑ j : Fin 3,
          Riemannian.chartChristoffel g a (e i) (e k) (e j)
            (extChartAt (𝓡 3) a p) •
              Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p := by
    calc
      _ = ∑ m : Fin (Module.finrank ℝ E3),
          Riemannian.chartChristoffel g a (e i) (e k) m
            (extChartAt (𝓡 3) a p) • X m p := hcov (e i) (e k) p hpU
      _ = ∑ m : Fin (Module.finrank ℝ E3),
          Riemannian.chartChristoffel g a (e i) (e k) m
            (extChartAt (𝓡 3) a p) •
              Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a m p := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [(hXev m).self_of_nhds]
      _ = ∑ j : Fin 3,
          Riemannian.chartChristoffel g a (e i) (e k) (e j)
            (extChartAt (𝓡 3) a p) •
              Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p := by
        rw [← Equiv.sum_comp e]
  have hassemble :
      (∑ k : Fin 3,
        (df k • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p +
          f k p • ∑ j : Fin 3,
            Riemannian.chartChristoffel g a (e i) (e k) (e j)
              (extChartAt (𝓡 3) a p) •
                Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p)) =
      ∑ k : Fin 3,
        (df k + ∑ l : Fin 3, f l p *
          Riemannian.chartChristoffel g a (e i) (e l) (e k)
            (extChartAt (𝓡 3) a p)) •
              Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p := by
    calc
      _ = (∑ k : Fin 3,
            df k • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p) +
          ∑ k : Fin 3, f k p • ∑ j : Fin 3,
            Riemannian.chartChristoffel g a (e i) (e k) (e j)
              (extChartAt (𝓡 3) a p) •
                Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p :=
        Finset.sum_add_distrib
      _ = (∑ k : Fin 3,
            df k • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p) +
          ∑ j : Fin 3, (∑ k : Fin 3, f k p *
            Riemannian.chartChristoffel g a (e i) (e k) (e j)
              (extChartAt (𝓡 3) a p)) •
                Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p := by
        congr 1
        calc
          _ = ∑ k : Fin 3, ∑ j : Fin 3,
              (f k p * Riemannian.chartChristoffel g a (e i) (e k) (e j)
                (extChartAt (𝓡 3) a p)) •
                  Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul]
          _ = ∑ j : Fin 3, ∑ k : Fin 3,
              (f k p * Riemannian.chartChristoffel g a (e i) (e k) (e j)
                (extChartAt (𝓡 3) a p)) •
                  Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p :=
            Finset.sum_comm
          _ = ∑ j : Fin 3, (∑ k : Fin 3, f k p *
              Riemannian.chartChristoffel g a (e i) (e k) (e j)
                (extChartAt (𝓡 3) a p)) •
                  Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_smul]
      _ = ∑ k : Fin 3,
          (df k + ∑ l : Fin 3, f l p *
            Riemannian.chartChristoffel g a (e i) (e l) (e k)
              (extChartAt (𝓡 3) a p)) •
                Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [add_smul]
  calc
    (g.leviCivitaConnection.cov
        (extendVector p (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)) V) p =
        (g.leviCivitaConnection.cov (X (e i)) V) p :=
      g.leviCivitaConnection.cov_congr_apply_left V hdir
    _ = ∑ k : Fin 3,
        ((df k) • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p +
          f k p • ∑ j : Fin 3,
            Riemannian.chartChristoffel g a (e i) (e k) (e j)
              (extChartAt (𝓡 3) a p) •
                Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) := by
      rw [cov_apply_of_eventuallyEq_sum_smul g.leviCivitaConnection
        (X (e i)) Finset.univ hf (fun k : Fin 3 => X (e k)) hloc]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hdircoeff k, hframecov k, (hXev (e k)).self_of_nhds]
    _ = ∑ k : Fin 3,
        (df k + ∑ l : Fin 3, f l p *
          Riemannian.chartChristoffel g a (e i) (e l) (e k)
            (extChartAt (𝓡 3) a p)) •
              Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p :=
      hassemble
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
