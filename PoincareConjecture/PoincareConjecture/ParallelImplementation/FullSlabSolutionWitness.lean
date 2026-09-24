import PoincareConjecture.ParallelImplementation.FullVectorDuhamelJet
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.SlabClampLinearExtension
import PoincareConjecture.ParallelImplementation.ForcingGraphHolderEstimate
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullSlabSolutionWitness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- A uniformly bounded actual solution jet for each slab forcing, with exposed value and residual. -/
theorem exists_full_slab_solution_witness (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ 1 →
      ∀ F : ForcingJet E6 T, F ∈ forcingGraph E6 T alpha →
      ∃ z : FullJet T, z ∈ fullParabolicJetSet T alpha hT.le ∧ ‖z‖ ≤ C*‖F‖ ∧
        (∀ (p : Slab T) (k : Fin 6), (z.1.1.1.1 p) k =
          ∫ s in (0:ℝ)..(p.1:ℝ), ∫ y : E3,
            euclideanHeatKernel 3 ((p.1:ℝ)-s) (p.2-y) *
              (F.1 (Set.projIcc 0 T hT.le s,y) k)) ∧
        ∀ p : Slab T, z.1.2 p - ∑ i : Fin 3,
          z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = F.1 p :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C₀, hC₀pos, hFull⟩ :=
    PoincareConjecture.ParallelImplementation.FullVectorDuhamelJet.full_vector_duhamel_jet
      alpha ha ha1
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro T hT hT1 F hF
  obtain ⟨E, hEnorm, hEvalue, hEnormEq, hEholder⟩ :=
    PoincareConjecture.ParallelImplementation.SlabClampLinearExtension.exists_slab_clamp_linear_extension
      E6 T hT.le
  let G : (ℝ × E3) →ᵇ E6 := E F.1
  have hFholder :=
    PoincareConjecture.ParallelImplementation.ForcingGraphHolderEstimate.forcing_graph_holder_bound
      T alpha ha F hF
  have hGholder : ∀ p q : Slab T,
      ‖G ((p.1 : ℝ), p.2) - G ((q.1 : ℝ), q.2)‖ ≤
        ‖F.2‖ *
          PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q ^ alpha := by
    intro p q
    have hh := hEholder alpha ‖F.2‖ ha (norm_nonneg _) F.1 hFholder
      ((p.1 : ℝ), p.2) ((q.1 : ℝ), q.2)
    simpa [G, PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho]
      using hh
  let u : ℝ → E3 → E6 := fun t x => WithLp.toLp 2 (fun k : Fin 6 =>
    ∫ s in (0 : ℝ)..t, ∫ y : E3,
      euclideanHeatKernel 3 (t-s) (x-y) * (G (s,y) k))
  obtain ⟨z, hz, hvalue, hresidual, hznorm⟩ :=
    hFull T ‖F.2‖ hT hT1 (norm_nonneg _) G hGholder
  change ∀ p : Slab T, z.1.1.1.1 p = u (p.1 : ℝ) p.2 at hvalue
  change (∀ p : Slab T, z.1.2 p =
      (∑ i : Fin 3, fderiv ℝ (fderiv ℝ (u (p.1 : ℝ))) p.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) +
        G ((p.1 : ℝ), p.2)) at hresidual
  have hGnorm : ‖G‖ = ‖F.1‖ := hEnormEq F.1
  have hF1norm : ‖F.1‖ ≤ ‖F‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hF2norm : ‖F.2‖ ≤ ‖F‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  have hsumNorm : ‖G‖ + ‖F.2‖ ≤ 2 * ‖F‖ := by
    rw [hGnorm]
    nlinarith
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · calc
      ‖z‖ ≤ C₀ * (‖G‖ + ‖F.2‖) := hznorm
      _ ≤ C₀ * (2 * ‖F‖) := mul_le_mul_of_nonneg_left hsumNorm hC₀pos.le
      _ = (2 * C₀) * ‖F‖ := by ring
  · intro p k
    calc
      z.1.1.1.1 p k = (u (p.1 : ℝ) p.2) k := congrArg (fun v : E6 => v k) (hvalue p)
      _ = ∫ s in (0 : ℝ)..(p.1 : ℝ), ∫ y : E3,
          euclideanHeatKernel 3 ((p.1 : ℝ)-s) (p.2-y) *
            (F.1 (Set.projIcc 0 T hT.le s, y) k) := by
        simp [u, G, hEvalue]
  · intro p
    have hu : ∀ x : E3, z.1.1.1.1 (p.1, x) = u (p.1 : ℝ) x := by
      intro x
      exact hvalue (p.1, x)
    have hspatial :=
      PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification.full_jet_spatial_identification
        T alpha hT.le z hz p.1 (fun x => u (p.1 : ℝ) x) hu
    have hGpoint : G ((p.1 : ℝ), p.2) = F.1 p := by
      rw [hEvalue]
      congr 1
      exact Prod.ext (Set.projIcc_val hT.le p.1) rfl
    have hsum :
        (∑ i : Fin 3, z.1.1.1.2.2 p
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
        (∑ i : Fin 3, fderiv ℝ (fderiv ℝ (u (p.1 : ℝ))) p.2
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg
        (fun A : E3 →L[ℝ] E3 →L[ℝ] E6 =>
          A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))
        (hspatial.2 p.2)
    rw [hresidual p, hsum, hGpoint]
    abel
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullSlabSolutionWitness
