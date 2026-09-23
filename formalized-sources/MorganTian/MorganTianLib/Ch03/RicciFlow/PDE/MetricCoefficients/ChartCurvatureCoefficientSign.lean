import MorganTianLib.Ch01.ChartCurvature
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureContraction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)

/-- **Math.** chart curvature coefficient sign. -/
theorem chart_curvature_coefficient_sign {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M) (y : E3)
    (hy : y ∈ (extChartAt (𝓡 3) a).target)
    (i j l k : Fin (Module.finrank ℝ E3)) :
    Riemannian.Geodesic.chartCoord (E := E3) k
      (MorganTianLib.chartCurvature g a y (Module.finBasis ℝ E3 i)
        (Module.finBasis ℝ E3 j) (Module.finBasis ℝ E3 l)) =
      Riemannian.Jacobi.chartCurvatureCoef g a j i l k y :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  haveI : Nontrivial E3 := inferInstance
  haveI : NeZero (Module.finrank ℝ E3) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  have hyInt : y ∈ interior (extChartAt (𝓡 3) a).target := by
    rw [(isOpen_extChartAt_target (I := 𝓡 3) a).interior_eq]
    exact hy
  have hδ (u v : Fin (Module.finrank ℝ E3)) :
      Riemannian.Geodesic.chartCoord (E := E3) u (Module.finBasis ℝ E3 v)
        = if v = u then (1 : ℝ) else 0 := by
    rw [Riemannian.Geodesic.chartCoord_def, Module.Basis.repr_self,
      Finsupp.single_apply]
  have hΓbasis (u v : Fin (Module.finrank ℝ E3)) :
      MorganTianLib.chartChristoffelBilin (I := 𝓡 3) g a y
          (Module.finBasis ℝ E3 u) (Module.finBasis ℝ E3 v)
        = ∑ m, Riemannian.chartChristoffel (I := 𝓡 3) g a u v m y •
            Module.finBasis ℝ E3 m := by
    rw [MorganTianLib.chartChristoffelBilin_apply,
      Riemannian.Geodesic.chartChristoffelContraction_def]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    simp only [hδ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hderiv (d u v : Fin (Module.finrank ℝ E3)) :
      fderiv ℝ (MorganTianLib.chartChristoffelBilin (I := 𝓡 3) g a) y
          (Module.finBasis ℝ E3 d)
          (Module.finBasis ℝ E3 u) (Module.finBasis ℝ E3 v)
        = ∑ m, (fderiv ℝ (Riemannian.chartChristoffel (I := 𝓡 3) g a u v m) y
            (Module.finBasis ℝ E3 d)) • Module.finBasis ℝ E3 m := by
    have hγdiff : ∀ b c m, HasFDerivAt
        (Riemannian.chartChristoffel (I := 𝓡 3) g a b c m)
        (fderiv ℝ (Riemannian.chartChristoffel (I := 𝓡 3) g a b c m) y) y := by
      intro b c m
      have h := ((Riemannian.chartChristoffel_contDiffOn_interior
        (I := 𝓡 3) g a b c m).contDiffAt
        (isOpen_interior.mem_nhds hyInt)).differentiableAt (by norm_num)
      exact h.hasFDerivAt
    have hD : HasFDerivAt (MorganTianLib.chartChristoffelBilin (I := 𝓡 3) g a)
        (∑ b, ∑ c, ∑ m,
          ((ContinuousLinearMap.smulRightL ℝ E3 (E3 →L[ℝ] E3)
              (Riemannian.Geodesic.chartCoordFunctional (E := E3) b)).comp
            (ContinuousLinearMap.smulRightL ℝ E3 E3
              (Riemannian.Geodesic.chartCoordFunctional (E := E3) c))).comp
          ((fderiv ℝ (Riemannian.chartChristoffel (I := 𝓡 3) g a b c m) y).smulRight
            (Module.finBasis ℝ E3 m))) y := by
      unfold MorganTianLib.chartChristoffelBilin
      exact HasFDerivAt.fun_sum fun b _ => HasFDerivAt.fun_sum fun c _ =>
        HasFDerivAt.fun_sum fun m _ => HasFDerivAt.comp
          (g := ⇑((ContinuousLinearMap.smulRightL ℝ E3 (E3 →L[ℝ] E3)
              (Riemannian.Geodesic.chartCoordFunctional (E := E3) b)).comp
            (ContinuousLinearMap.smulRightL ℝ E3 E3
              (Riemannian.Geodesic.chartCoordFunctional (E := E3) c))))
          (f := fun z => Riemannian.chartChristoffel (I := 𝓡 3) g a b c m z •
            Module.finBasis ℝ E3 m)
          y (ContinuousLinearMap.hasFDerivAt _)
          ((hγdiff b c m).smul_const (Module.finBasis ℝ E3 m))
    rw [hD.fderiv]
    have hδ' : ∀ b c : Fin (Module.finrank ℝ E3),
        Riemannian.Geodesic.chartCoordFunctional (E := E3) b
            (Module.finBasis ℝ E3 c) = if c = b then (1 : ℝ) else 0 := by
      intro b c
      rw [Riemannian.Geodesic.chartCoordFunctional_apply,
        Riemannian.Geodesic.chartCoord_def, Module.Basis.repr_self,
        Finsupp.single_apply]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRightL_apply_apply, hδ', ite_smul, one_smul,
      zero_smul, apply_ite (fun f : E3 →L[ℝ] E3 =>
        f (Module.finBasis ℝ E3 v)), ContinuousLinearMap.zero_apply,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hR :
      MorganTianLib.chartCurvature (I := 𝓡 3) g a y
          (Module.finBasis ℝ E3 i) (Module.finBasis ℝ E3 j)
          (Module.finBasis ℝ E3 l)
        = ∑ m,
          (Riemannian.partialDeriv (E := E3) i
              (Riemannian.chartChristoffel (I := 𝓡 3) g a j l m) y
            - Riemannian.partialDeriv (E := E3) j
              (Riemannian.chartChristoffel (I := 𝓡 3) g a i l m) y
            + ∑ r,
                (Riemannian.chartChristoffel (I := 𝓡 3) g a j l r y *
                    Riemannian.chartChristoffel (I := 𝓡 3) g a i r m y
                  - Riemannian.chartChristoffel (I := 𝓡 3) g a i l r y *
                    Riemannian.chartChristoffel (I := 𝓡 3) g a j r m y)) •
            Module.finBasis ℝ E3 m := by
    rw [MorganTianLib.chartCurvature_def,
      MorganTianLib.christoffelCurvature]
    rw [hderiv i j l, hderiv j i l, hΓbasis j l, hΓbasis i l, map_sum, map_sum]
    simp only [map_smul, Riemannian.partialDeriv]
    simp_rw [hΓbasis]
    refine (Module.finBasis ℝ E3).ext_elem fun m₀ => ?_
    simp only [map_add, map_sub, map_sum, map_smul, Module.Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add,
      Finsupp.coe_sub, Finsupp.coe_finset_sum, Pi.add_apply, Pi.sub_apply,
      Finset.sum_apply, Finsupp.smul_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite,
      mul_zero, mul_one, smul_eq_mul]
    rw [Finset.sum_sub_distrib]
    ring_nf
  rw [hR]
  simp only [Riemannian.Geodesic.chartCoord_def, map_sum, map_smul,
    Module.Basis.repr_self, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ]
  simp only [Riemannian.Jacobi.chartCurvatureCoef, if_true]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
