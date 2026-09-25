import PoincareConjecture.ParallelImplementation.NonlinearForcingHessianProduct
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AffineForcingGraphBilinearProduct
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_affine_forcing_bilinear_product
    {Y V W Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T alpha R K : ℝ) (hR : 0 < R) (hK : 0 ≤ K)
    (X : Submodule ℝ (ForcingJet Z T))
    (hX : (X : Set (ForcingJet Z T)) = forcingGraph Z T alpha)
    (B : V →L[ℝ] W →L[ℝ] Z)
    (a0 : ForcingJet V T) (h0 : ForcingJet W T)
    (ha0 : a0 ∈ forcingGraph V T alpha) (hh0 : h0 ∈ forcingGraph W T alpha)
    (J : Y → ForcingJet V T) (hJ0 : J 0 = 0)
    (hJ : ∀ z, ‖z‖ ≤ R → J z ∈ forcingGraph V T alpha)
    (hJL : ∀ z w, ‖z‖ ≤ R → ‖w‖ ≤ R → ‖J z-J w‖ ≤ K*‖z-w‖)
    (Q : Y →L[ℝ] ForcingJet W T) (hQ : ∀ z, Q z ∈ forcingGraph W T alpha) :
    ∃ N : Y → X,
      (∀ z, ‖z‖ ≤ R → ∀ p : Slab T,
        (N z).1.1 p = B ((a0+J z).1 p) ((h0+Q z).1 p)) ∧
      ‖N 0‖ ≤ 2*‖B‖*‖a0‖*‖h0‖ ∧
      ∀ z w, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖N z-N w‖ ≤
          (2*‖B‖*(K*(‖h0‖+‖Q‖*R)+(‖a0‖+K*R)*‖Q‖))*‖z-w‖ :=
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
  have haddGraphV (f g : ForcingJet V T)
      (hf : f ∈ forcingGraph V T alpha)
      (hg : g ∈ forcingGraph V T alpha) : f + g ∈ forcingGraph V T alpha := by
    intro p
    change f.2 p + g.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((f.1 p.1.1 + g.1 p.1.1) - (f.1 p.1.2 + g.1 p.1.2))
    rw [hf p, hg p]
    simp only [smul_add, smul_sub]
    abel
  have haddGraphW (f g : ForcingJet W T)
      (hf : f ∈ forcingGraph W T alpha)
      (hg : g ∈ forcingGraph W T alpha) : f + g ∈ forcingGraph W T alpha := by
    intro p
    change f.2 p + g.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((f.1 p.1.1 + g.1 p.1.1) - (f.1 p.1.2 + g.1 p.1.2))
    rw [hf p, hg p]
    simp only [smul_add, smul_sub]
    abel
  have hzeroZ : (0 : ForcingJet Z T) ∈ forcingGraph Z T alpha := by
    intro p
    simp
  have hzeroX : (0 : ForcingJet Z T) ∈ (X : Set (ForcingJet Z T)) := by
    rw [hX]
    exact hzeroZ
  let a (z : Y) : ForcingJet V T := a0 + J z
  let b (z : Y) : ForcingJet W T := h0 + Q z
  have ha (z : Y) (hz : ‖z‖ ≤ R) : a z ∈ forcingGraph V T alpha := by
    change a0 + J z ∈ forcingGraph V T alpha
    exact haddGraphV a0 (J z) ha0 (hJ z hz)
  have hb (z : Y) : b z ∈ forcingGraph W T alpha := by
    change h0 + Q z ∈ forcingGraph W T alpha
    exact haddGraphW h0 (Q z) hh0 (hQ z)
  let N : Y → X := fun z =>
    if hz : ‖z‖ ≤ R then
      ⟨M (a z) (ha z hz) (b z), by
        have hmem : M (a z) (ha z hz) (b z) ∈ forcingGraph Z T alpha :=
          (hM (a z) (ha z hz)).2.2.2 (b z) (hb z)
        rw [← hX] at hmem
        exact hmem⟩
    else ⟨0, hzeroX⟩
  have hNval (z : Y) (hz : ‖z‖ ≤ R) :
      (N z : ForcingJet Z T) = M (a z) (ha z hz) (b z) := by
    simp [N, hz]
  have hzeroBall : ‖(0 : Y)‖ ≤ R := by
    simpa using hR.le
  refine ⟨N, ?_, ?_, ?_⟩
  · intro z hz p
    rw [hNval z hz]
    exact (hM (a z) (ha z hz)).2.1 (b z) p
  · calc
      ‖N 0‖ = ‖M a0 ha0 h0‖ := by
        change ‖(N 0 : ForcingJet Z T)‖ = _
        rw [hNval 0 hzeroBall]
        simp [a, b, hJ0, Q.map_zero]
      _ ≤ ‖M a0 ha0‖ * ‖h0‖ := (M a0 ha0).le_opNorm h0
      _ ≤ (2 * ‖B‖ * ‖a0‖) * ‖h0‖ :=
        mul_le_mul_of_nonneg_right (hM a0 ha0).1 (norm_nonneg h0)
      _ = 2 * ‖B‖ * ‖a0‖ * ‖h0‖ := by ring
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
    have hacoef : a z - a w = J z - J w := by
      dsimp [a]
      abel
    have hcoefGraph : a z - a w ∈ forcingGraph V T alpha := by
      rw [hacoef]
      exact hJsub
    have hbinput : b z - b w = Q z - Q w := by
      dsimp [b]
      abel
    have hcoef1 (p : Slab T) :
        (a z - a w).1 p = (a z).1 p - (a w).1 p := by
      change ((a z).1 - (a w).1) p = (a z).1 p - (a w).1 p
      rw [BoundedContinuousFunction.sub_apply]
    have hinput1 (p : Slab T) :
        (b z - b w).1 p = (b z).1 p - (b w).1 p := by
      change ((b z).1 - (b w).1) p = (b z).1 p - (b w).1 p
      rw [BoundedContinuousFunction.sub_apply]
    have hinputSub : b z - b w ∈ forcingGraph W T alpha := by
      rw [hbinput, ← Q.map_sub]
      exact hQ (z - w)
    let Pz : ForcingJet Z T := M (a z) (ha z hz) (b z)
    let Pw : ForcingJet Z T := M (a w) (ha w hw) (b w)
    let U : ForcingJet Z T := M (a z) (ha z hz) (b z - b w)
    let V' : ForcingJet Z T := M (a z - a w) hcoefGraph (b w)
    have hPz : Pz ∈ forcingGraph Z T alpha :=
      (hM (a z) (ha z hz)).2.2.2 (b z) (hb z)
    have hPw : Pw ∈ forcingGraph Z T alpha :=
      (hM (a w) (ha w hw)).2.2.2 (b w) (hb w)
    have hU : U ∈ forcingGraph Z T alpha :=
      (hM (a z) (ha z hz)).2.2.2 (b z - b w) hinputSub
    have hV' : V' ∈ forcingGraph Z T alpha :=
      (hM (a z - a w) hcoefGraph).2.2.2 (b w) (hb w)
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
      rw [(hM (a z) (ha z hz)).2.1 (b z) p,
        (hM (a w) (ha w hw)).2.1 (b w) p,
        (hM (a z) (ha z hz)).2.1 (b z - b w) p,
        (hM (a z - a w) hcoefGraph).2.1 (b w) p,
        hinput1 p, hcoef1 p]
      calc
        B ((a z).1 p) ((b z).1 p) - B ((a w).1 p) ((b w).1 p) =
            (B ((a z).1 p) ((b z).1 p) - B ((a z).1 p) ((b w).1 p)) +
              (B ((a z).1 p) ((b w).1 p) - B ((a w).1 p) ((b w).1 p)) := by
                abel
        _ = B ((a z).1 p) ((b z).1 p - (b w).1 p) +
              B ((a z).1 p - (a w).1 p) ((b w).1 p) := by
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
    have haNorm : ‖a z‖ ≤ ‖a0‖ + K * ‖z‖ := by
      dsimp [a]
      calc
        ‖a0 + J z‖ ≤ ‖a0‖ + ‖J z‖ := norm_add_le _ _
        _ ≤ ‖a0‖ + K * ‖z‖ := by linarith [hJzNorm]
    have habDiffNorm : ‖a z - a w‖ ≤ K * ‖z - w‖ := by
      rw [hacoef]
      exact hJdiffNorm
    have hbwNorm : ‖b w‖ ≤ ‖h0‖ + ‖Q‖ * ‖w‖ := by
      dsimp [b]
      calc
        ‖h0 + Q w‖ ≤ ‖h0‖ + ‖Q w‖ := norm_add_le _ _
        _ ≤ ‖h0‖ + ‖Q‖ * ‖w‖ := by linarith [hQwNorm]
    calc
      ‖N z - N w‖ = ‖Pz - Pw‖ := by
        change ‖(N z : ForcingJet Z T) - (N w : ForcingJet Z T)‖ = _
        rw [hNval z hz, hNval w hw]
      _ = ‖U + V'‖ := by rw [hidentity]
      _ ≤ ‖U‖ + ‖V'‖ := norm_add_le _ _
      _ ≤ ‖M (a z) (ha z hz)‖ * ‖b z - b w‖ +
            ‖M (a z - a w) hcoefGraph‖ * ‖b w‖ := by
        exact add_le_add
          ((M (a z) (ha z hz)).le_opNorm (b z - b w))
          ((M (a z - a w) hcoefGraph).le_opNorm (b w))
      _ ≤ (2 * ‖B‖ * ‖a z‖) * ‖b z - b w‖ +
            (2 * ‖B‖ * ‖a z - a w‖) * ‖b w‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hM (a z) (ha z hz)).1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hM (a z - a w) hcoefGraph).1 (norm_nonneg _))
      _ ≤ (2 * ‖B‖ * (‖a0‖ + K * ‖z‖)) *
            (‖Q‖ * ‖z - w‖) +
          (2 * ‖B‖ * (K * ‖z - w‖)) *
            (‖h0‖ + ‖Q‖ * ‖w‖) := by
        rw [hbinput]
        gcongr
      _ ≤ (2 * ‖B‖ * (‖a0‖ + K * R)) *
            (‖Q‖ * ‖z - w‖) +
          (2 * ‖B‖ * (K * ‖z - w‖)) *
            (‖h0‖ + ‖Q‖ * R) := by
        have haR : ‖a0‖ + K * ‖z‖ ≤ ‖a0‖ + K * R := by
          gcongr
        have hbR : ‖h0‖ + ‖Q‖ * ‖w‖ ≤ ‖h0‖ + ‖Q‖ * R := by
          gcongr
        gcongr
      _ = (2 * ‖B‖ *
            (K * (‖h0‖ + ‖Q‖ * R) + (‖a0‖ + K * R) * ‖Q‖)) *
            ‖z - w‖ := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AffineForcingGraphBilinearProduct
