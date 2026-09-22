import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelSpatialLipschitz
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatSpatialLipschitz
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedNemytskiiOperator
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
theorem semilinear_mild_spatial_regularization : ∃ C : ℝ, 0<C ∧
    ∀ (f : E3 →ᵇ ℝ) (N : ℝ → ℝ) (L T : ℝ), 0≤L → 0≤T →
      (∀ a b : ℝ, |N a-N b| ≤ L*|a-b|) → ∀ u : (ℝ × E3) →ᵇ ℝ,
      (∀ t : ℝ, 0<t → t≤T → ∀ x : E3,
        u (t,x)=(∫ y : E3, euclideanHeatKernel 3 t y*f (x-y))+
          ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) y*N (u (s,x-y))) →
      ∀ t : ℝ, 0<t → t≤T → ∀ x z : E3,
        |u (t,x)-u (t,z)| ≤ C*(‖f‖/Real.sqrt t+
          (|N 0|+L*‖u‖)*Real.sqrt t)*‖x-z‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C₁, hC₁, hheat⟩ := bounded_heat_spatial_lipschitz
  obtain ⟨C₂, hC₂, hduhamel⟩ := duhamel_spatial_lipschitz
  let C : ℝ := C₁ + C₂
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro f N L T hL hT hN u hu t ht htT x z
  obtain ⟨A, hA, hAnorm, hAlip⟩ := bounded_nemytskii_operator N L hL hN
  have hfree (a : E3) :
      (∫ y : E3, euclideanHeatKernel 3 t y * f (a-y)) =
        ∫ y : E3, euclideanHeatKernel 3 t (a-y) * f y := by
    let p : E3 → ℝ := fun y => euclideanHeatKernel 3 t y * f (a-y)
    have hmap :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) a).integral_comp
        (MeasurableEquiv.subLeft a).measurableEmbedding p
    calc
      (∫ y : E3, euclideanHeatKernel 3 t y * f (a-y)) = ∫ y : E3, p y := by rfl
      _ = ∫ y : E3, p (a-y) := hmap.symm
      _ = ∫ y : E3, euclideanHeatKernel 3 t (a-y) * f y := by
        congr 1
        funext y
        dsimp [p]
        rw [sub_sub_cancel]
  have hsource (a : E3) :
      (∫ s in (0:ℝ)..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * N (u (s,a-y))) =
        ∫ s in (0:ℝ)..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * (A u) (s,a-y) := by
    simp_rw [hA]
  have hux := hu t ht htT x
  have huz := hu t ht htT z
  rw [hfree x, hsource x] at hux
  rw [hfree z, hsource z] at huz
  have hheat_bound := hheat f t ht x z
  have hduhamel_bound := hduhamel (A u) t (le_of_lt ht) x z
  have hduhamel_bound' :
      |(∫ s in (0:ℝ)..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * (A u) (s,x-y)) -
        (∫ s in (0:ℝ)..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * (A u) (s,z-y))| ≤
        C₂ * (|N 0| + L * ‖u‖) * Real.sqrt t * ‖x-z‖ := by
    calc
      _ ≤ C₂ * ‖A u‖ * Real.sqrt t * ‖x-z‖ := hduhamel_bound
      _ ≤ C₂ * (|N 0| + L * ‖u‖) * Real.sqrt t * ‖x-z‖ := by
        have hB : 0 ≤ |N 0| + L * ‖u‖ :=
          (norm_nonneg (A u)).trans (hAnorm u)
        gcongr
        exact hAnorm u
  calc
    |u (t,x) - u (t,z)| =
        |((∫ y : E3, euclideanHeatKernel 3 t (x-y) * f y) -
            (∫ y : E3, euclideanHeatKernel 3 t (z-y) * f y)) +
          ((∫ s in (0:ℝ)..t, ∫ y : E3,
            euclideanHeatKernel 3 (t-s) y * (A u) (s,x-y)) -
            (∫ s in (0:ℝ)..t, ∫ y : E3,
            euclideanHeatKernel 3 (t-s) y * (A u) (s,z-y)))| := by
              rw [hux, huz]
              ring_nf
    _ ≤ C₁ * ‖f‖ * ‖x-z‖ / Real.sqrt t +
          C₂ * (|N 0| + L * ‖u‖) * Real.sqrt t * ‖x-z‖ := by
            calc
              _ ≤ |(∫ y : E3, euclideanHeatKernel 3 t (x-y) * f y) -
                  (∫ y : E3, euclideanHeatKernel 3 t (z-y) * f y)| +
                    |(∫ s in (0:ℝ)..t, ∫ y : E3,
                      euclideanHeatKernel 3 (t-s) y * (A u) (s,x-y)) -
                      (∫ s in (0:ℝ)..t, ∫ y : E3,
                      euclideanHeatKernel 3 (t-s) y * (A u) (s,z-y))| :=
                abs_add_le _ _
              _ ≤ _ := add_le_add hheat_bound hduhamel_bound'
    _ ≤ C * (‖f‖ / Real.sqrt t +
          (|N 0| + L * ‖u‖) * Real.sqrt t) * ‖x-z‖ := by
      have hB : 0 ≤ |N 0| + L * ‖u‖ :=
        (norm_nonneg (A u)).trans (hAnorm u)
      have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
      have hdist : 0 ≤ ‖x-z‖ := norm_nonneg _
      have hnormf : 0 ≤ ‖f‖ := norm_nonneg _
      have ha : 0 ≤ ‖f‖ / Real.sqrt t := by positivity
      have hb : 0 ≤ (|N 0| + L * ‖u‖) * Real.sqrt t :=
        mul_nonneg hB hsqrt
      have hinner :
          C₁ * (‖f‖ / Real.sqrt t) +
              C₂ * ((|N 0| + L * ‖u‖) * Real.sqrt t) ≤
            (C₁ + C₂) * (‖f‖ / Real.sqrt t +
              (|N 0| + L * ‖u‖) * Real.sqrt t) := by
        nlinarith [mul_nonneg (le_of_lt hC₁) hb,
          mul_nonneg (le_of_lt hC₂) ha]
      calc
        C₁ * ‖f‖ * ‖x-z‖ / Real.sqrt t +
            C₂ * (|N 0| + L * ‖u‖) * Real.sqrt t * ‖x-z‖ =
          (C₁ * (‖f‖ / Real.sqrt t) +
            C₂ * ((|N 0| + L * ‖u‖) * Real.sqrt t)) * ‖x-z‖ := by ring
        _ ≤ (C₁ + C₂) * (‖f‖ / Real.sqrt t +
              (|N 0| + L * ‖u‖) * Real.sqrt t) * ‖x-z‖ :=
          mul_le_mul_of_nonneg_right hinner hdist
        _ = C * (‖f‖ / Real.sqrt t +
              (|N 0| + L * ‖u‖) * Real.sqrt t) * ‖x-z‖ := by
          rfl
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
