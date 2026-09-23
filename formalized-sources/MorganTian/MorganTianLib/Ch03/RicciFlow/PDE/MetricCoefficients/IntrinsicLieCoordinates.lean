import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ScalarReparametrizedChartDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientMetricPairing
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LeviCivitaComponentDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartScalarComponentExtensions
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateLieCovariant
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ReparametrizedActualChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartOperatorSymmetry
import MorganTianLib.Ch03.RicciFlow.Soliton
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** intrinsic lie eq coordinate. -/
theorem intrinsic_lie_eq_coordinate {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (W : E3 → E3) (U : Set E3) (hU : IsOpen U) (hxU : x ∈ U)
    (hW : ContDiffOn ℝ ∞ W U) (V : Riemannian.SmoothVectorField (𝓡 3) M)
    (hV : ∀ᶠ q : M in 𝓝 ((extChartAt (𝓡 3) a).symm (B x)),
      V q = ∑ k : Fin 3, W (B.symm (extChartAt (𝓡 3) a q)) k •
        Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q) (i j : Fin 3) :
    let p := (extChartAt (𝓡 3) a).symm (B x);
    let G : E3 → (E3 →L[ℝ] E3) := fun z =>
      chartCoefficientOperator g a ((extChartAt (𝓡 3) a).symm (B z)) e;
    MorganTianLib.metricLieDerivativeAt g V p
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) =
      coordinateLieMetricExpr G W x i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let φ := extChartAt (𝓡 3) a
  let p : M := φ.symm (B x)
  let G : E3 → (E3 →L[ℝ] E3) := fun z =>
    chartCoefficientOperator g a (φ.symm (B z)) e
  let u : Fin 3 → E3 := fun r => EuclideanSpace.single r 1
  let P : Fin 3 → E3 →L[ℝ] E3 := fun r => fderiv ℝ G x (u r)
  obtain ⟨f, hf, hfeq⟩ :=
    chart_scalar_component_extensions g a e B hB x hx W U hU hxU hW
  have hpChart : p ∈ (chartAt E3 a).source := by
    change (extChartAt (𝓡 3) a).symm (B x) ∈ (chartAt E3 a).source
    simpa [extChartAt_source] using (extChartAt (𝓡 3) a).map_target hx
  have hpφ : φ p = B x := by
    dsimp [p]
    exact φ.right_inv hx
  have hbase : p ∈ (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := by
    change p ∈ (chartAt E3 a).source
    exact hpChart
  obtain ⟨c, hc, hpos0, _⟩ := chart_coefficient_coercivity g a p e hbase
  have hpos : ∀ v : E3, c * ‖v‖ ^ 2 ≤ inner ℝ (G x v) v := by
    intro v
    simpa [G, p, φ] using hpos0 v
  have hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3,
      inner ℝ (G y v) w = inner ℝ v (G y w) := by
    filter_upwards with y
    intro v w
    exact chart_operator_selfadjoint g a (φ.symm (B y)) e v w
  have hGself (v w : E3) :
      inner ℝ (G x v) w = inner ℝ v (G x w) := by
    exact chart_operator_selfadjoint g a p e v w
  let F : E3 → E3 →L[ℝ] E3 := fun z =>
    chartCoefficientOperator g a (φ.symm z) e
  have hBcont : ContDiffAt ℝ ∞ (fun z : E3 => B z) x :=
    B.toContinuousLinearMap.contDiff.contDiffAt
  have hGdiff : DifferentiableAt ℝ G x := by
    have hGcont : ContDiffAt ℝ ∞ G x := by
      change ContDiffAt ℝ ∞ (F ∘ fun z : E3 => B z) x
      exact (chart_operator_contDiffAt g a e (B x) hx).comp x hBcont
    exact hGcont.differentiableAt (by norm_num)
  have hWdiff : DifferentiableAt ℝ W x := by
    exact (hW.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
  have hqCont : ContinuousAt (fun y : E3 => φ.symm (B y)) x := by
    have hs : ContMDiffAt 𝓘(ℝ, E3) (𝓡 3) ∞ φ.symm (B x) :=
      ((contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) a (B x) hx).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) a).mem_nhds hx))
    exact hs.continuousAt.comp hBcont.continuousAt
  have hqTendsto : Tendsto (fun y : E3 => φ.symm (B y)) (𝓝 x) (𝓝 p) := by
    change Tendsto (fun y : E3 => φ.symm (B y)) (𝓝 x)
      (𝓝 (φ.symm (B x)))
    exact hqCont
  have hBtarget : ∀ᶠ y : E3 in 𝓝 x, B y ∈ φ.target := by
    exact hBcont.continuousAt.eventually
      ((isOpen_extChartAt_target (I := 𝓡 3) a).mem_nhds hx)
  have hVloc : ∀ᶠ q : M in 𝓝 p, V q =
      ∑ k : Fin 3, f k q •
        Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q := by
    filter_upwards [hV, hfeq] with q hq hqf
    calc
      V q = ∑ k : Fin 3, W (B.symm (φ q)) k •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q := hq
      _ = ∑ k : Fin 3, f k q •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) q := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← hqf k]
  have hfeqk (k : Fin 3) :
      (fun q : M => f k q) =ᶠ[𝓝 p] (fun q => W (B.symm (φ q)) k) := by
    filter_upwards [hfeq] with q hq
    exact hq k
  have hcoordEq (k : Fin 3) :
      (fun y : E3 => f k (φ.symm (B y))) =ᶠ[𝓝 x] (fun y => W y k) := by
    have hpull := (hfeqk k).comp_tendsto hqTendsto
    filter_upwards [hpull, hBtarget] with y hy hyt
    change f k (φ.symm (B y)) = W (B.symm (φ (φ.symm (B y)))) k at hy
    rw [φ.right_inv hyt] at hy
    simpa using hy
  have hscalarDeriv (k i : Fin 3) :
      fderiv ℝ (fun y : E3 => f k (φ.symm (B y))) x (u i) =
        mfderiv (𝓡 3) 𝓘(ℝ) (f k) p
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p) := by
    simpa [u, p, φ] using
      (scalar_reparametrized_chart_derivative g a e B hB x hx (f k) (hf k) i)
  have hprojDeriv (k : Fin 3) :
      fderiv ℝ (fun y : E3 => W y k) x =
        (EuclideanSpace.proj k).comp (fderiv ℝ W x) := by
    have h := ((hasFDerivAt_const (x := x) (c := EuclideanSpace.proj k)).clm_apply
      hWdiff.hasFDerivAt).fderiv
    simpa [Function.comp_def] using h
  have hderivW (k i : Fin 3) :
      fderiv ℝ W x (u i) k =
        mfderiv (𝓡 3) 𝓘(ℝ) (f k) p
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p) := by
    calc
      fderiv ℝ W x (u i) k =
          (EuclideanSpace.proj k) (fderiv ℝ W x (u i)) := rfl
      _ = fderiv ℝ (fun y : E3 => W y k) x (u i) := by
        rw [hprojDeriv k]
        rfl
      _ = fderiv ℝ (fun y : E3 => f k (φ.symm (B y))) x (u i) := by
        exact congrArg (fun L : E3 →L[ℝ] ℝ => L (u i))
          (hcoordEq k).fderiv_eq.symm
      _ = mfderiv (𝓡 3) 𝓘(ℝ) (f k) p
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p) :=
        hscalarDeriv k i
  have hfpoint (k : Fin 3) : f k p = W x k := by
    have hh := hfeq.self_of_nhds k
    change f k p = W (B.symm (φ p)) k at hh
    rw [hpφ, B.symm_apply_apply] at hh
    exact hh
  let df : Fin 3 → Fin 3 → ℝ := fun r k =>
    mfderiv (𝓡 3) 𝓘(ℝ) (f k) p
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e r) p)
  have hdf (r k : Fin 3) : df r k = fderiv ℝ W x (u r) k := by
    dsimp [df]
    exact (hderivW k r).symm
  have hγ (k i l : Fin 3) :
      coordinateChristoffel (G x) P k i l =
        Riemannian.chartChristoffel g a (e i) (e l) (e k) (φ p) := by
    rw [hpφ]
    exact reparametrized_actual_christoffel g a e B hB x hx k i l
  have hcoeff (i k : Fin 3) :
      (df i k + ∑ l : Fin 3, f l p *
        Riemannian.chartChristoffel g a (e i) (e l) (e k) (φ p)) =
      (fderiv ℝ W x (u i) + connectionVector (G x) P (u i) (W x)) k := by
    calc
      _ = fderiv ℝ W x (u i) k +
          ∑ l : Fin 3, coordinateChristoffel (G x) P k i l * W x l := by
        rw [hdf i k]
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        rw [← hγ k i l, hfpoint l]
        ring
      _ = (fderiv ℝ W x (u i) + connectionVector (G x) P (u i) (W x)) k := by
        simp [connectionVector, u, PiLp.single_apply]
  have hcovFormula (i : Fin 3) :
      (g.leviCivitaConnection.cov
        (MorganTianLib.extendVector p
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)) V) p =
        ∑ k : Fin 3,
          (fderiv ℝ W x (u i) + connectionVector (G x) P (u i) (W x)) k •
            Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p := by
    have hLC := levi_civita_component_derivative g a p hpChart e V f hf hVloc i
    dsimp only at hLC
    change (g.leviCivitaConnection.cov
        (MorganTianLib.extendVector p
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)) V) p =
      ∑ k : Fin 3,
        (df i k + ∑ l : Fin 3, f l p *
          Riemannian.chartChristoffel g a (e i) (e l) (e k) (φ p)) •
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p at hLC
    calc
      _ = ∑ k : Fin 3,
          (df i k + ∑ l : Fin 3, f l p *
              Riemannian.chartChristoffel g a (e i) (e l) (e k) (φ p)) •
            Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p := hLC
      _ = ∑ k : Fin 3,
          (fderiv ℝ W x (u i) + connectionVector (G x) P (u i) (W x)) k •
            Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hcoeff i k]
  have hstandard (j : Fin 3) :
      (∑ k : Fin 3, (u j) k •
        Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p) =
        Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p := by
    classical
    calc
      _ = ∑ k : Fin 3, if k = j then
          (1 : ℝ) • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p
          else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hkj : k = j
        · subst k
          simp [u]
        · simp [u, hkj]
      _ = Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p := by
        simp
  let D : Fin 3 → E3 := fun i =>
    fderiv ℝ W x (u i) + connectionVector (G x) P (u i) (W x)
  have hpair (i j : Fin 3) :
      g.metricInner p
          ((g.leviCivitaConnection.cov
            (MorganTianLib.extendVector p
              (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)) V) p)
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) =
        inner ℝ (G x (D i)) (u j) := by
    rw [hcovFormula i]
    calc
      _ = g.metricInner p
          (∑ k : Fin 3, (D i) k •
            Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p)
          (∑ k : Fin 3, (u j) k •
            Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p) := by
              rw [hstandard j]
      _ = inner ℝ (chartCoefficientOperator g a p e (D i)) (u j) :=
        chart_coefficient_metric_pairing g a p e (D i) (u j)
      _ = inner ℝ (G x (D i)) (u j) := by rfl
  have hpairSym (i j : Fin 3) :
      g.metricInner p
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
          ((g.leviCivitaConnection.cov
            (MorganTianLib.extendVector p
              (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p)) V) p) =
        inner ℝ (G x (u i)) (D j) := by
    calc
      _ = g.metricInner p
          ((g.leviCivitaConnection.cov
            (MorganTianLib.extendVector p
              (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p)) V) p)
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p) :=
        g.metricInner_comm p _ _
      _ = inner ℝ (G x (D j)) (u i) := hpair j i
      _ = inner ℝ (G x (u i)) (D j) := by
        calc
          _ = inner ℝ (u i) (G x (D j)) := real_inner_comm _ _
          _ = inner ℝ (G x (u i)) (D j) := (hGself (u i) (D j)).symm
  have hLieCov :
      MorganTianLib.metricLieDerivativeAt g V p
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) =
        inner ℝ (G x (D i)) (u j) + inner ℝ (G x (u i)) (D j) := by
    unfold MorganTianLib.metricLieDerivativeAt
    rw [hpair i j, hpairSym i j]
  have hcov := coordinate_lie_metric_covariant G W x hGdiff hWdiff hsym c hc hpos i j
  calc
    MorganTianLib.metricLieDerivativeAt g V p
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) =
        inner ℝ (G x (D i)) (u j) + inner ℝ (G x (u i)) (D j) := hLieCov
    _ = coordinateLieMetricExpr G W x i j := by
      simpa [D, u] using hcov.symm
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
