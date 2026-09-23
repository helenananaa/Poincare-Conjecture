import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DuhamelHessianSpatialHolder
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** actual duhamel spatial schauder. -/
theorem actual_duhamel_spatial_schauder 
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ), 0 ≤ L → 0 < T →
      (∀ s ∈ Icc (0:ℝ) T, ∀ x z : E3, |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha) →
      let u : E3 → ℝ := fun x => ∫ s in (0:ℝ)..T, ∫ y : E3,
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s) (x-y)*F (s,y);
      ContDiff ℝ 2 u ∧ (∀ (x : E3) (i j : Fin 3),
        |fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)| ≤ C*L*T^(alpha/2)) ∧
      ∀ (x z : E3) (i j : Fin 3),
        |fderiv ℝ (fun w => fderiv ℝ u w (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)-
         fderiv ℝ (fun w => fderiv ℝ u w (EuclideanSpace.single i 1)) z (EuclideanSpace.single j 1)| ≤ C*L*‖x-z‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₁, hC₁, hfull⟩ :=
    MorganTianLib.ParabolicPDE.full_duhamel_spatial_C2 alpha ha ha1
  obtain ⟨C₂, hC₂, hspatial⟩ := duhamel_hessian_spatial_holder alpha ha ha1
  let C : ℝ := max C₁ C₂
  have hC : 0 < C := by
    dsimp [C]
    exact lt_max_of_lt_left hC₁
  refine ⟨C, hC, ?_⟩
  intro F L T hL hT hholder
  let u : E3 → ℝ := fun x => ∫ s in (0:ℝ)..T, ∫ y : E3,
    MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s) (x-y)*F (s,y)
  have hC2 := hfull F L T hL hT hholder
  have hu : ContDiff ℝ 2 u := by
    simpa [u] using hC2.1
  have hident := hC2.2
  have hderiv_id (x : E3) (i j : Fin 3) :
      fderiv ℝ (fun w => fderiv ℝ u w (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) =
        ∫ s in (0:ℝ)..T, ∫ y : E3,
          heatHessian3 (T-s) i j y * F (s,x-y) := by
    simpa [u, heatHessian3] using (hident x i j).1
  refine ⟨hu, ?_, ?_⟩
  · intro x i j
    calc
      |fderiv ℝ (fun w => fderiv ℝ u w (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)| ≤ C₁ * L * T^(alpha/2) :=
        (hident x i j).2
      _ ≤ C * L * T^(alpha/2) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right
          · exact le_max_left _ _
          · exact hL
        · exact Real.rpow_nonneg hT.le _
  · intro x z i j
    rw [hderiv_id x i j, hderiv_id z i j]
    calc
      |(∫ s in (0:ℝ)..T, ∫ y : E3,
          heatHessian3 (T-s) i j y * F (s,x-y)) -
        (∫ s in (0:ℝ)..T, ∫ y : E3,
          heatHessian3 (T-s) i j y * F (s,z-y))| ≤
          C₂ * L * ‖x-z‖^alpha := hspatial F L T hL hT.le hholder x z i j
      _ ≤ C * L * ‖x-z‖^alpha := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right
          · exact le_max_right _ _
          · exact hL
        · exact Real.rpow_nonneg (norm_nonneg _) _
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
