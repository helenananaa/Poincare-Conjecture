import Mathlib
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ChartMetricPullbackPairings
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_chart_metric_pullback_pairings
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) M) (p : M) :

    ∃ b : E3 → (E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ),
      (∀ y v w : E3, b y v w=g.metricInner ((extChartAt 𝓘(ℝ, E3) p).symm y) ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) v) ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) w)) ∧
      ∀ i j : Fin 3, ContDiffOn ℝ ∞
        (fun y => b y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (extChartAt 𝓘(ℝ, E3) p).target :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let φ := extChartAt 𝓘(ℝ, E3) p
  let D : E3 → E3 →ₗ[ℝ] E3 := fun y =>
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) φ.symm y).toLinearMap
  let b : E3 → (E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ) := fun y =>
    LinearMap.mk₂ ℝ
      (fun v w => g.metricInner (φ.symm y) (D y v) (D y w))
      (by
        intro v₁ v₂ w
        rw [map_add, g.metricInner_add_left])
      (by
        intro c v w
        change g.metricInner (φ.symm y) (D y (c • v)) (D y w) = _
        rw [map_smul, g.metricInner_smul_left, smul_eq_mul])
      (by
        intro v w₁ w₂
        rw [map_add, g.metricInner_add_right])
      (by
        intro c v w
        change g.metricInner (φ.symm y) (D y v) (D y (c • w)) = _
        rw [map_smul, g.metricInner_smul_right, smul_eq_mul])
  refine ⟨b, ?_, ?_⟩
  · intro y v w
    change g.metricInner (φ.symm y) (D y v) (D y w) = _
    rfl
  · intro i j
    let β : Module.Basis (Fin (Module.finrank ℝ E3)) ℝ E3 := Module.finBasis ℝ E3
    let ci : Fin (Module.finrank ℝ E3) → ℝ := β.repr (EuclideanSpace.single i 1)
    let cj : Fin (Module.finrank ℝ E3) → ℝ := β.repr (EuclideanSpace.single j 1)
    let G : Fin (Module.finrank ℝ E3) → Fin (Module.finrank ℝ E3) → E3 → ℝ :=
      fun k l y => Riemannian.chartGramOnE (I := 𝓘(ℝ, E3)) g p k l y
    have hframe {y : E3} (hy : y ∈ φ.target) (k : Fin (Module.finrank ℝ E3)) :
        D y (β k) =
          Riemannian.Tensor.chartBasisVecFiber (I := 𝓘(ℝ, E3)) p k (φ.symm y) := by
      change mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y (β k) = _
      have hphi : φ.symm y = (chartAt E3 p).symm y := by
        change (extChartAt 𝓘(ℝ, E3) p).symm y = _
        rw [extChartAt_coe_symm]
        simp
      -- The inverse chart differential is the chart-frame vector: apply the
      -- chart differential and use its two-sided chain rule on the open target.
      let x := (extChartAt 𝓘(ℝ, E3) p).symm y
      have hxsrc : x ∈ (chartAt E3 p).source := by
        dsimp [x]
        have h := (extChartAt 𝓘(ℝ, E3) p).map_target hy
        rwa [extChartAt_source] at h
      have hxext : x ∈ (extChartAt 𝓘(ℝ, E3) p).source := by
        rwa [extChartAt_source]
      have hchart : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3)
          (extChartAt 𝓘(ℝ, E3) p) x := mdifferentiableAt_extChartAt hxsrc
      have hsymm : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3)
          (extChartAt 𝓘(ℝ, E3) p).symm y := by
        have h := mdifferentiableWithinAt_extChartAt_symm
          (I := 𝓘(ℝ, E3)) (x := p) hy
        simpa [mdifferentiableWithinAt_univ] using h
      have hcomp := mfderiv_comp y hchart hsymm
      have hround : (extChartAt 𝓘(ℝ, E3) p) ∘ (extChartAt 𝓘(ℝ, E3) p).symm
          =ᶠ[𝓝 y] id := by
        filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E3)) p).mem_nhds hy]
          with z hz
        exact (extChartAt 𝓘(ℝ, E3) p).right_inv hz
      have hid : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3)
          ((extChartAt 𝓘(ℝ, E3) p) ∘ (extChartAt 𝓘(ℝ, E3) p).symm) y =
          ContinuousLinearMap.id ℝ E3 := by
        rw [hround.mfderiv_eq]
        exact mfderiv_id
      have hcompid :
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p) x).comp
            (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p).symm y) =
          ContinuousLinearMap.id ℝ E3 := hcomp.symm.trans hid
      have hinj : Function.Injective
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p) x) :=
        (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E3)) hxext).injective
      have hframeChart :
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (extChartAt 𝓘(ℝ, E3) p) x
            (Riemannian.Tensor.chartBasisVecFiber (I := 𝓘(ℝ, E3)) p k x) = β k := by
        have hb : x ∈ (trivializationAt E3
            (TangentSpace (𝓘(ℝ, E3))) p).baseSet := by
          rw [TangentBundle.trivializationAt_baseSet]
          exact hxsrc
        rw [← TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℝ, E3)) hxsrc]
        have ht := Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
          (trivializationAt E3 (TangentSpace (𝓘(ℝ, E3))) p) hb
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓘(ℝ, E3)) p k x)
        rw [Riemannian.Tensor.trivializationAt_chartBasisVec_snd] at ht
        · exact ht
        · exact hb
      rw [hphi]
      apply hinj
      dsimp [x] at hcompid hinj hframeChart ⊢
      rw [hframeChart, ← ContinuousLinearMap.comp_apply, hcompid]
      rfl
    have hgram {y : E3} (hy : y ∈ φ.target)
        (k l : Fin (Module.finrank ℝ E3)) :
        (b y (β k)) (β l) = G k l y := by
      change g.metricInner (φ.symm y) (D y (β k)) (D y (β l)) = _
      rw [hframe hy k, hframe hy l]
      rfl
    have hformula (y : E3) (hy : y ∈ φ.target) :
        b y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
          ∑ k, ci k * (∑ l, cj l * G k l y) := by
      rw [← LinearMap.sum_repr_mul_repr_mul β β (B := b y)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)]
      simp [Finsupp.sum_fintype, smul_eq_mul, ci, cj, hgram hy]
      simp_rw [Finset.mul_sum]
    have hsum : ContDiffOn ℝ ∞
        (fun y => ∑ k, ci k * (∑ l, cj l * G k l y)) φ.target := by
      refine ContDiffOn.sum (fun k _ => ?_)
      refine (contDiffOn_const (c := ci k)).mul ?_
      refine ContDiffOn.sum (fun l _ => ?_)
      exact (contDiffOn_const (c := cj l)).mul
        (Riemannian.chartGramOnE_contDiffOn (I := 𝓘(ℝ, E3)) g p k l)
    exact hsum.congr (fun y hy => hformula y hy)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ChartMetricPullbackPairings
