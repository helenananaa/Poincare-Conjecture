import PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.NonlinearForcingHessianProduct
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_nonlinear_forcing_hessian_product
    {Y V W Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T alpha R K : ℝ) (hR : 0 < R) (hK : 0 ≤ K)
    (X : Submodule ℝ (ForcingJet Z T))
    (hX : (X : Set (ForcingJet Z T)) = forcingGraph Z T alpha)
    (B : V →L[ℝ] W →L[ℝ] Z)
    (J : Y → ForcingJet V T) (hJ0 : J 0=0)
    (hJ : ∀ z, ‖z‖ ≤ R → J z ∈ forcingGraph V T alpha)
    (hJL : ∀ z w, ‖z‖ ≤ R → ‖w‖ ≤ R → ‖J z-J w‖ ≤ K*‖z-w‖)
    (Q : Y →L[ℝ] ForcingJet W T) (hQ : ∀ z, Q z ∈ forcingGraph W T alpha) :
    ∃ N : Y → X, N 0=0 ∧
      (∀ z, ‖z‖ ≤ R → ∀ p : Slab T, (N z).1.1 p = B ((J z).1 p) ((Q z).1 p)) ∧
      (∀ z w, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖N z-N w‖ ≤ (2*‖B‖*K*‖Q‖)*(‖z‖+‖w‖)*‖z-w‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let M (a : ForcingJet V T) (ha : a ∈ forcingGraph V T alpha) :
      ForcingJet W T →L[ℝ] ForcingJet Z T :=
    Classical.choose
      (PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        B T alpha a ha)
  have hM (a : ForcingJet V T) (ha : a ∈ forcingGraph V T alpha) :=
    Classical.choose_spec
      (PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        B T alpha a ha)
  have hzeroZ : (0 : ForcingJet Z T) ∈ forcingGraph Z T alpha := by
    intro p
    simp
  have hzeroX : (0 : ForcingJet Z T) ∈ (X : Set (ForcingJet Z T)) := by
    rw [hX]
    exact hzeroZ
  let N : Y → X := fun z =>
    if hz : ‖z‖ ≤ R then
      ⟨M (J z) (hJ z hz) (Q z), by
        have hmem : M (J z) (hJ z hz) (Q z) ∈ forcingGraph Z T alpha :=
          (hM (J z) (hJ z hz)).2.2.2 (Q z) (hQ z)
        rw [← hX] at hmem
        exact hmem⟩
    else ⟨0, hzeroX⟩
  have hNval (z : Y) (hz : ‖z‖ ≤ R) :
      (N z : ForcingJet Z T) = M (J z) (hJ z hz) (Q z) := by
    simp [N, hz]
  have hzeroBall : ‖(0 : Y)‖ ≤ R := by
    simpa using hR.le
  refine ⟨N, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (N 0 : ForcingJet Z T) = 0
    rw [hNval 0 hzeroBall]
    rw [Q.map_zero]
    exact (M (J 0) (hJ 0 hzeroBall)).map_zero
  · intro z hz p
    rw [hNval z hz]
    exact (hM (J z) (hJ z hz)).2.1 (Q z) p
  · intro z w hz hw
    have hJsub : J z - J w ∈ forcingGraph V T alpha := by
      intro p
      change (J z).2 p - (J w).2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((J z).1 p.1.1 - (J w).1 p.1.1 -
            ((J z).1 p.1.2 - (J w).1 p.1.2))
      rw [hJ z hz p, hJ w hw p]
      simp only [smul_sub]
      abel
    have hJsub1 (p : Slab T) :
        (J z - J w).1 p = (J z).1 p - (J w).1 p := by
      change ((J z).1 - (J w).1) p = (J z).1 p - (J w).1 p
      rw [BoundedContinuousFunction.sub_apply]
    have hQsub1 (p : Slab T) :
        (Q z - Q w).1 p = (Q z).1 p - (Q w).1 p := by
      change ((Q z).1 - (Q w).1) p = (Q z).1 p - (Q w).1 p
      rw [BoundedContinuousFunction.sub_apply]
    let Pz : ForcingJet Z T := M (J z) (hJ z hz) (Q z)
    let Pw : ForcingJet Z T := M (J w) (hJ w hw) (Q w)
    let U : ForcingJet Z T := M (J z) (hJ z hz) (Q z - Q w)
    let V' : ForcingJet Z T := M (J z - J w) hJsub (Q w)
    have hPz : Pz ∈ forcingGraph Z T alpha :=
      (hM (J z) (hJ z hz)).2.2.2 (Q z) (hQ z)
    have hPw : Pw ∈ forcingGraph Z T alpha :=
      (hM (J w) (hJ w hw)).2.2.2 (Q w) (hQ w)
    have hU : U ∈ forcingGraph Z T alpha :=
      (hM (J z) (hJ z hz)).2.2.2 (Q z - Q w) (by
        have hq : Q z - Q w ∈ forcingGraph W T alpha := by
          rw [← Q.map_sub]
          exact hQ (z - w)
        exact hq)
    have hV' : V' ∈ forcingGraph Z T alpha :=
      (hM (J z - J w) hJsub).2.2.2 (Q w) (hQ w)
    have hleftGraph : Pz - Pw ∈ forcingGraph Z T alpha := by
      intro p
      change Pz.2 p - Pw.2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          (Pz.1 p.1.1 - Pw.1 p.1.1 - (Pz.1 p.1.2 - Pw.1 p.1.2))
      rw [hPz p, hPw p]
      simp only [smul_sub]
      abel
    have hrightGraph : U + V' ∈ forcingGraph Z T alpha := by
      intro p
      change U.2 p + V'.2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((U.1 p.1.1 + V'.1 p.1.1) - (U.1 p.1.2 + V'.1 p.1.2))
      rw [hU p, hV' p]
      simp only [smul_add, smul_sub]
      abel
    have hidentity : Pz - Pw = U + V' := by
      apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
        T alpha (Pz - Pw) (U + V') hleftGraph hrightGraph
      intro p
      change Pz.1 p - Pw.1 p = U.1 p + V'.1 p
      dsimp only [Pz, Pw, U, V']
      rw [(hM (J z) (hJ z hz)).2.1 (Q z) p,
        (hM (J w) (hJ w hw)).2.1 (Q w) p,
        (hM (J z) (hJ z hz)).2.1 (Q z - Q w) p,
        (hM (J z - J w) hJsub).2.1 (Q w) p,
        hQsub1 p, hJsub1 p]
      calc
        B ((J z).1 p) ((Q z).1 p) - B ((J w).1 p) ((Q w).1 p) =
            (B ((J z).1 p) ((Q z).1 p) - B ((J z).1 p) ((Q w).1 p)) +
              (B ((J z).1 p) ((Q w).1 p) - B ((J w).1 p) ((Q w).1 p)) := by
                abel
        _ = B ((J z).1 p) ((Q z).1 p - (Q w).1 p) +
              B ((J z).1 p - (J w).1 p) ((Q w).1 p) := by
                rw [← map_sub, ← B.map_sub₂]
    have hJzNorm : ‖J z‖ ≤ K * ‖z‖ := by
      calc
        ‖J z‖ = ‖J z - J 0‖ := by rw [hJ0]; simp
        _ ≤ K * ‖z - 0‖ := hJL z 0 hz hzeroBall
        _ = K * ‖z‖ := by simp
    have hJdiffNorm : ‖J z - J w‖ ≤ K * ‖z - w‖ := hJL z w hz hw
    have hQdiffNorm : ‖Q z - Q w‖ ≤ ‖Q‖ * ‖z - w‖ := by
      rw [← Q.map_sub]
      exact Q.le_opNorm (z - w)
    have hQwNorm : ‖Q w‖ ≤ ‖Q‖ * ‖w‖ := Q.le_opNorm w
    calc
      ‖N z - N w‖ = ‖Pz - Pw‖ := by
        change ‖(N z : ForcingJet Z T) - (N w : ForcingJet Z T)‖ = _
        rw [hNval z hz, hNval w hw]
      _ = ‖U + V'‖ := by rw [hidentity]
      _ ≤ ‖U‖ + ‖V'‖ := norm_add_le _ _
      _ ≤ ‖M (J z) (hJ z hz)‖ * ‖Q z - Q w‖ +
            ‖M (J z - J w) hJsub‖ * ‖Q w‖ := by
        exact add_le_add
          ((M (J z) (hJ z hz)).le_opNorm (Q z - Q w))
          ((M (J z - J w) hJsub).le_opNorm (Q w))
      _ ≤ (2 * ‖B‖ * ‖J z‖) * ‖Q z - Q w‖ +
            (2 * ‖B‖ * ‖J z - J w‖) * ‖Q w‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hM (J z) (hJ z hz)).1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hM (J z - J w) hJsub).1 (norm_nonneg _))
      _ ≤ (2 * ‖B‖ * (K * ‖z‖)) * (‖Q‖ * ‖z - w‖) +
            (2 * ‖B‖ * (K * ‖z - w‖)) * (‖Q‖ * ‖w‖) := by
        gcongr
      _ = (2 * ‖B‖ * K * ‖Q‖) * (‖z‖ + ‖w‖) * ‖z - w‖ := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.NonlinearForcingHessianProduct
