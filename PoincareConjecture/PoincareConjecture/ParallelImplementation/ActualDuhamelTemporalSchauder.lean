import PoincareConjecture.ParallelImplementation.DuhamelHessianTemporalHolder
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ActualDuhamelTemporalSchauder
open MorganTianLib.MetricCoefficient
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Temporal Schauder control for actual second spatial derivatives, including initial time. -/
theorem actual_duhamel_temporal_schauder
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L t h : ℝ), 0 ≤ L → 0 ≤ t → 0 < h →
      (∀ s ∈ Icc (0:ℝ) (t+h), ∀ x z : E3, |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha) →
      let u : ℝ → E3 → ℝ := fun T x => ∫ s in (0:ℝ)..T, ∫ y : E3,
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T-s) (x-y) * F (s,y)
      ∀ (x : E3) (i j : Fin 3),
      |fderiv ℝ (fun z => fderiv ℝ (u (t+h)) z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) -
       fderiv ℝ (fun z => fderiv ℝ (u t) z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)| ≤
        C * L * h^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C, hC, htemp⟩ :=
    PoincareConjecture.ParallelImplementation.DuhamelHessianTemporalHolder.duhamel_hessian_temporal_holder
      alpha ha ha1
  obtain ⟨Csp, hCsp, hsp⟩ :=
    MorganTianLib.ParabolicPDE.full_duhamel_spatial_C2 alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro F L t h hL ht hh hholder u x i j
  have hrepr : ∀ T, 0 ≤ T → T ≤ t + h → ∀ x i j,
      (fderiv ℝ (fun z => fderiv ℝ (u T) z (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) =
        ∫ s in (0:ℝ)..T, ∫ y : E3,
          heatHessian3 (T-s) i j y * F (s,x-y) := by
    intro T hT hTle x i j
    by_cases hT0 : T = 0
    · subst T
      simp [u, heatHessian3]
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hholderT : ∀ s ∈ Icc (0:ℝ) T, ∀ x z : E3,
          |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha := by
        intro s hs x z
        apply hholder s
        exact ⟨hs.1, hs.2.trans hTle⟩
      have hformula := ((hsp F L T hL hTpos hholderT).2 x i j).1
      simpa [u, heatHessian3] using hformula
  have hfuture : ∀ x i j,
      (fderiv ℝ (fun z => fderiv ℝ (u (t+h)) z (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) =
        ∫ s in (0:ℝ)..(t+h), ∫ y : E3,
          heatHessian3 (t+h-s) i j y * F (s,x-y) := by
    apply hrepr
    · linarith
    · exact le_rfl
  have hpast : ∀ x i j,
      (fderiv ℝ (fun z => fderiv ℝ (u t) z (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) =
        ∫ s in (0:ℝ)..t, ∫ y : E3,
          heatHessian3 (t-s) i j y * F (s,x-y) := by
    apply hrepr
    · exact ht
    · linarith
  calc
    |(fderiv ℝ (fun z => fderiv ℝ (u (t+h)) z (EuclideanSpace.single i 1)) x)
         (EuclideanSpace.single j 1) -
       (fderiv ℝ (fun z => fderiv ℝ (u t) z (EuclideanSpace.single i 1)) x)
         (EuclideanSpace.single j 1)| =
      |(∫ s in (0:ℝ)..(t+h), ∫ y : E3,
          heatHessian3 (t+h-s) i j y * F (s,x-y)) -
       (∫ s in (0:ℝ)..t, ∫ y : E3,
          heatHessian3 (t-s) i j y * F (s,x-y))| := by
        rw [hfuture x i j, hpast x i j]
    _ ≤ C * L * h^(alpha/2) := htemp F L t h hL ht hh hholder x i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ActualDuhamelTemporalSchauder
