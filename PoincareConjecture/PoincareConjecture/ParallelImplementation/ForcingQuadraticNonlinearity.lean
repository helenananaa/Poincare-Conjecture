import PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingQuadraticNonlinearity
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
/-- Actual quadratic forcing has a full Holder-graph local Lipschitz estimate. -/
theorem exists_forcing_quadratic_nonlinearity
    {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : V →L[ℝ] V →L[ℝ] Z) (T alpha : ℝ) :
    ∃ N : ForcingJet V T → ForcingJet Z T, N 0 = 0 ∧
      ∀ f ∈ forcingGraph V T alpha,
        N f ∈ forcingGraph Z T alpha ∧
        (∀ p : Slab T, (N f).1 p = B (f.1 p) (f.1 p)) ∧
        (∀ p : Pair T, (N f).2 p =
          B (f.1 p.1.1) (f.2 p) + B (f.2 p) (f.1 p.1.2)) ∧
        ‖N f‖ ≤ 2 * ‖B‖ * ‖f‖^2 ∧
        ∀ g ∈ forcingGraph V T alpha,
          ‖N f-N g‖ ≤ 2 * ‖B‖ * (‖f‖+‖g‖) * ‖f-g‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let M (f : ForcingJet V T) (hf : f ∈ forcingGraph V T alpha) :
      ForcingJet V T →L[ℝ] ForcingJet Z T :=
    Classical.choose
      (PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        B T alpha f hf)
  have hM (f : ForcingJet V T) (hf : f ∈ forcingGraph V T alpha) :=
    Classical.choose_spec
      (PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        B T alpha f hf)
  let N : ForcingJet V T → ForcingJet Z T := fun f =>
    if hf : f ∈ forcingGraph V T alpha then M f hf f else 0
  have hN_eq (f : ForcingJet V T) (hf : f ∈ forcingGraph V T alpha) :
      N f = M f hf f := by
    simp [N, hf]
  refine ⟨N, ?_, ?_⟩
  · have h0 : (0 : ForcingJet V T) ∈ forcingGraph V T alpha := by
      intro p
      simp
    rw [hN_eq 0 h0]
    exact (M 0 h0).map_zero
  · intro f hf
    have hNf := hN_eq f hf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hNf]
      exact (hM f hf).2.2.2 f hf
    · intro p
      rw [hNf]
      exact (hM f hf).2.1 f p
    · intro p
      rw [hNf]
      exact (hM f hf).2.2.1 f p
    · calc
        ‖N f‖ = ‖M f hf f‖ := by rw [hNf]
        _ ≤ ‖M f hf‖ * ‖f‖ := (M f hf).le_opNorm f
        _ ≤ (2 * ‖B‖ * ‖f‖) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (hM f hf).1 (norm_nonneg f)
        _ = 2 * ‖B‖ * ‖f‖ ^ 2 := by ring
    · intro g hg
      have hd : f - g ∈ forcingGraph V T alpha := by
        intro p
        change f.2 p - g.2 p =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            ((f.1 p.1.1 - g.1 p.1.1) - (f.1 p.1.2 - g.1 p.1.2))
        rw [hf p, hg p]
        simp only [smul_sub]
        abel
      have hsub1 (x : Slab T) : (f - g).1 x = f.1 x - g.1 x := by
        change (f.1 - g.1) x = f.1 x - g.1 x
        rw [BoundedContinuousFunction.sub_apply]
      have hsub2 (p : Pair T) : (f - g).2 p = f.2 p - g.2 p := by
        change (f.2 - g.2) p = f.2 p - g.2 p
        rw [BoundedContinuousFunction.sub_apply]
      have hNg := hN_eq g hg
      have hidentity :
          N f - N g = M f hf (f - g) + M (f - g) hd g := by
        rw [hNf, hNg]
        apply Prod.ext
        · apply BoundedContinuousFunction.ext
          intro p
          change (M f hf f).1 p - (M g hg g).1 p =
            (M f hf (f - g)).1 p + (M (f - g) hd g).1 p
          dsimp only [M]
          rw [(hM f hf).2.1 f p, (hM g hg).2.1 g p,
            (hM f hf).2.1 (f - g) p,
            (hM (f - g) hd).2.1 g p, hsub1 p]
          calc
            B (f.1 p) (f.1 p) - B (g.1 p) (g.1 p) =
                (B (f.1 p) (f.1 p) - B (f.1 p) (g.1 p)) +
                  (B (f.1 p) (g.1 p) - B (g.1 p) (g.1 p)) := by abel
            _ = B (f.1 p) (f.1 p - g.1 p) +
                B (f.1 p - g.1 p) (g.1 p) := by
                  rw [← map_sub, ← B.map_sub₂]
        · apply BoundedContinuousFunction.ext
          intro p
          change (M f hf f).2 p - (M g hg g).2 p =
            (M f hf (f - g)).2 p + (M (f - g) hd g).2 p
          dsimp only [M]
          rw [(hM f hf).2.2.1 f p, (hM g hg).2.2.1 g p,
            (hM f hf).2.2.1 (f - g) p,
            (hM (f - g) hd).2.2.1 g p,
            hsub2 p, hsub1 p.1.1, hsub1 p.1.2]
          simp only [map_sub, sub_apply]
          abel
      calc
        ‖N f - N g‖ =
            ‖M f hf (f - g) + M (f - g) hd g‖ := by rw [hidentity]
        _ ≤ ‖M f hf (f - g)‖ + ‖M (f - g) hd g‖ := norm_add_le _ _
        _ ≤ ‖M f hf‖ * ‖f - g‖ + ‖M (f - g) hd‖ * ‖g‖ :=
          add_le_add ((M f hf).le_opNorm (f - g))
            ((M (f - g) hd).le_opNorm g)
        _ ≤ (2 * ‖B‖ * ‖f‖) * ‖f - g‖ +
              (2 * ‖B‖ * ‖f - g‖) * ‖g‖ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hM f hf).1 (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_right (hM (f - g) hd).1 (norm_nonneg _)
        _ = 2 * ‖B‖ * (‖f‖ + ‖g‖) * ‖f - g‖ := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingQuadraticNonlinearity
