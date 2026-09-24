import PoincareConjecture.ParallelImplementation.SlabForcingExtension
import PoincareConjecture.ParallelImplementation.DuhamelForcedHeatEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ClippedDuhamelOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SlabForcedHeatExistence
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Construct a bounded classical forced heat solution from data given only on a finite slab. -/
theorem slab_forced_heat_existence (T alpha H : ℝ)
    (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1) (hH : 0 ≤ H)
    (F : Slab T →ᵇ ℝ)
    (hholder : ∀ p q : Slab T, |F p-F q| ≤ H*parabolicRho p q ^ alpha) :
    ∃ u : ℝ → E3 → ℝ, u 0 = 0 ∧
      ContinuousOn (fun p : ℝ × E3 => u p.1 p.2) (Icc (0:ℝ) T ×ˢ Set.univ) ∧
      (∀ t ∈ Icc (0:ℝ) T, ContDiff ℝ 2 (u t)) ∧
      (∀ t : Icc (0:ℝ) T, ∀ x : E3, |u (t:ℝ) x| ≤ T*‖F‖) ∧
      ∀ t : Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ x : E3,
        HasDerivAt (fun s => u s x)
          ((∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (u (t:ℝ)) y
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) + F (t,x)) (t:ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  have hFholder_norm : ∀ p q : Slab T,
      ‖F p - F q‖ ≤ H * parabolicRho p q ^ alpha := by
    intro p q
    simpa [Real.norm_eq_abs] using hholder p q
  obtain ⟨G, hGslab, hGnorm, hGholder⟩ :=
    PoincareConjecture.ParallelImplementation.SlabForcingExtension.slab_forcing_extension
      T alpha H hT.le ha hH F hFholder_norm
  have hGspace : ∀ s : ℝ, ∀ x y : E3,
      |G (s,x) - G (s,y)| ≤ H * ‖x-y‖ ^ alpha := by
    intro s x y
    simpa [Real.norm_eq_abs] using hGholder (s,x) (s,y)
  let u : ℝ → E3 → ℝ := fun t x => ∫ s in (0:ℝ)..t,
    ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * G (s,y)
  obtain ⟨D, hD, hDbound, _⟩ := clipped_duhamel_operator T hT.le
  have hchange (s t : ℝ) (x : E3) :
      (∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * G (s,y)) =
        ∫ y : E3, euclideanHeatKernel 3 (t-s) y * G (s,x-y) := by
    let g : E3 → ℝ := fun y => euclideanHeatKernel 3 (t-s) y * G (s,x-y)
    have hcomp :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding g
    calc
      (∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * G (s,y)) =
          ∫ y : E3, g (x-y) := by
            congr 1
            funext y
            simp [g]
      _ = ∫ y : E3, g y := hcomp
      _ = ∫ y : E3, euclideanHeatKernel 3 (t-s) y * G (s,x-y) := rfl
  have hDformula (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (x : E3) :
      (D G) (t,x) = u t x := by
    rw [hD G (t,x)]
    simp only [min_eq_right ht.2, max_eq_right ht.1]
    dsimp [u]
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hchange s t x).symm
  have hPDE := PoincareConjecture.ParallelImplementation.DuhamelForcedHeatEquation.duhamel_forced_heat_equation
    alpha ha ha1 G H T hH hT
    (by
      intro s hs x y
      exact hGspace s x y)
  have hu0 : u 0 = 0 := by
    have h := hPDE.1
    simpa [u] using h
  have hcontinuous :
      ContinuousOn (fun p : ℝ × E3 => u p.1 p.2) (Icc (0:ℝ) T ×ˢ Set.univ) := by
    have hDG : Continuous (fun p : ℝ × E3 => (D G) p) := (D G).continuous
    apply hDG.continuousOn.congr
    intro p hp
    symm
    exact hDformula p.1 hp.1 p.2
  obtain ⟨C, hCpos, hC⟩ := full_duhamel_spatial_C2 alpha ha ha1
  have hC2 : ∀ t ∈ Icc (0:ℝ) T, ContDiff ℝ 2 (u t) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hzero : u 0 = fun _ : E3 => 0 := by
        funext x
        simp [u]
      rw [hzero]
      exact contDiff_const
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have htemp := hC G H t hH htpos (by
        intro s hs x y
        exact hGspace s x y)
      simpa [u] using htemp.1
  refine ⟨u, hu0, hcontinuous, ?_, ?_, ?_⟩
  · intro t ht
    exact hC2 t ht
  · intro t x
    calc
      |u (t:ℝ) x| = ‖u (t:ℝ) x‖ := (Real.norm_eq_abs _).symm
      _ = ‖(D G) ((t:ℝ),x)‖ := by rw [← hDformula (t:ℝ) t.property x]
      _ ≤ ‖D G‖ := BoundedContinuousFunction.norm_coe_le_norm (D G) ((t:ℝ),x)
      _ ≤ T * ‖G‖ := hDbound G
      _ = T * ‖F‖ := by rw [hGnorm]
  · intro t ht0 htT x
    have ht : (t:ℝ) ∈ Ioo (0:ℝ) T := ⟨ht0, htT⟩
    have hderiv := hPDE.2 (t:ℝ) ht x
    convert hderiv using 1
    have hsource : G ((t:ℝ),x) = F (t,x) := hGslab t x
    rw [hsource]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SlabForcedHeatExistence
