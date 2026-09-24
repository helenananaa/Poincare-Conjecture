import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphInverseLipschitz
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
theorem forcing_graph_inverse_lipschitz
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (T : ℝ) (a c b d : ForcingJet A T) (M R : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hb : ∀ p : Slab T, b.1 p*(1-a.1 p)=1)
    (hd : ∀ p : Slab T, (1-c.1 p)*d.1 p=1)
    (hbi : ∀ p : Pair T, b.2 p = b.1 p.1.1*a.2 p*b.1 p.1.2)
    (hdi : ∀ p : Pair T, d.2 p = d.1 p.1.1*c.2 p*d.1 p.1.2)
    (hbN : ‖b.1‖ ≤ M) (hdN : ‖d.1‖ ≤ M)
    (haN : ‖a.2‖ ≤ R) (hcN : ‖c.2‖ ≤ R) :
    ‖b-d‖ ≤ (M^2+2*M^3*R)*‖a-c‖ :=
/- SWARM_PROOF_BEGIN -/
by
  let δ : ℝ := ‖a-c‖
  let K : ℝ := M^2 + 2*M^3*R
  have hδ : 0 ≤ δ := norm_nonneg _
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hM2K : M^2 ≤ K := by
    have htail : 0 ≤ 2*M^3*R := by positivity
    dsimp [K]
    linarith
  have hres (p : Slab T) :
      b.1 p-d.1 p = b.1 p*(a.1 p-c.1 p)*d.1 p := by
    have hba : b.1 p*a.1 p = b.1 p-1 := by
      calc
        b.1 p*a.1 p = b.1 p-b.1 p*(1-a.1 p) := by noncomm_ring
        _ = b.1 p-1 := by rw [hb p]
    have hcd : c.1 p*d.1 p = d.1 p-1 := by
      calc
        c.1 p*d.1 p = d.1 p-(1-c.1 p)*d.1 p := by noncomm_ring
        _ = d.1 p-1 := by rw [hd p]
    calc
      b.1 p-d.1 p = (b.1 p*a.1 p)*d.1 p-b.1 p*(c.1 p*d.1 p) := by
        rw [hba, hcd]
        noncomm_ring
      _ = b.1 p*(a.1 p-c.1 p)*d.1 p := by noncomm_ring
  have hbPoint (p : Slab T) : ‖b.1 p‖ ≤ M := by
    exact (BoundedContinuousFunction.norm_coe_le_norm b.1 p).trans hbN
  have hdPoint (p : Slab T) : ‖d.1 p‖ ≤ M := by
    exact (BoundedContinuousFunction.norm_coe_le_norm d.1 p).trans hdN
  have ha2Point (p : Pair T) : ‖a.2 p‖ ≤ R := by
    exact (BoundedContinuousFunction.norm_coe_le_norm a.2 p).trans haN
  have hc2Point (p : Pair T) : ‖c.2 p‖ ≤ R := by
    exact (BoundedContinuousFunction.norm_coe_le_norm c.2 p).trans hcN
  have harg (p : Slab T) : ‖a.1 p-c.1 p‖ ≤ δ := by
    change ‖a.1 p-c.1 p‖ ≤ ‖a-c‖
    calc
      ‖a.1 p-c.1 p‖ = ‖(a-c).1 p‖ := by simp
      _ ≤ ‖(a-c).1‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ ‖a-c‖ := norm_fst_le _
  have harg2 (p : Pair T) : ‖a.2 p-c.2 p‖ ≤ δ := by
    change ‖a.2 p-c.2 p‖ ≤ ‖a-c‖
    calc
      ‖a.2 p-c.2 p‖ = ‖(a-c).2 p‖ := by simp
      _ ≤ ‖(a-c).2‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ ‖a-c‖ := norm_snd_le _
  have hval (p : Slab T) : ‖b.1 p-d.1 p‖ ≤ M^2*δ := by
    calc
      ‖b.1 p-d.1 p‖ = ‖b.1 p*(a.1 p-c.1 p)*d.1 p‖ := by rw [hres p]
      _ ≤ ‖b.1 p‖*‖a.1 p-c.1 p‖*‖d.1 p‖ := by
        calc
          ‖b.1 p*(a.1 p-c.1 p)*d.1 p‖ ≤
              ‖b.1 p*(a.1 p-c.1 p)‖*‖d.1 p‖ := norm_mul_le _ _
          _ ≤ (‖b.1 p‖*‖a.1 p-c.1 p‖)*‖d.1 p‖ := by
            exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ M*δ*M := by
        calc
          ‖b.1 p‖*‖a.1 p-c.1 p‖*‖d.1 p‖ ≤ M*‖a.1 p-c.1 p‖*‖d.1 p‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hbPoint p) (norm_nonneg _)) (norm_nonneg _)
          _ ≤ M*δ*‖d.1 p‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (harg p) hM) (norm_nonneg _)
          _ ≤ M*δ*M :=
            mul_le_mul_of_nonneg_left (hdPoint p) (mul_nonneg hM hδ)
      _ = M^2*δ := by ring
  have hdecomp (p : Pair T) :
      b.2 p-d.2 p =
        (b.1 p.1.1-d.1 p.1.1)*a.2 p*b.1 p.1.2 +
        d.1 p.1.1*(a.2 p-c.2 p)*b.1 p.1.2 +
        d.1 p.1.1*c.2 p*(b.1 p.1.2-d.1 p.1.2) := by
    rw [hbi p, hdi p]
    noncomm_ring
  have hderivPoint (p : Pair T) :
      ‖b.2 p-d.2 p‖ ≤ K*δ := by
    let X : A := (b.1 p.1.1-d.1 p.1.1)*a.2 p*b.1 p.1.2
    let Y : A := d.1 p.1.1*(a.2 p-c.2 p)*b.1 p.1.2
    let Z : A := d.1 p.1.1*c.2 p*(b.1 p.1.2-d.1 p.1.2)
    have hX : ‖X‖ ≤ M^3*R*δ := by
      dsimp [X]
      calc
        ‖(b.1 p.1.1-d.1 p.1.1)*a.2 p*b.1 p.1.2‖ ≤
            ‖b.1 p.1.1-d.1 p.1.1‖*‖a.2 p‖*‖b.1 p.1.2‖ := by
          calc
            ‖(b.1 p.1.1-d.1 p.1.1)*a.2 p*b.1 p.1.2‖ ≤
                ‖(b.1 p.1.1-d.1 p.1.1)*a.2 p‖*‖b.1 p.1.2‖ := norm_mul_le _ _
            _ ≤ (‖b.1 p.1.1-d.1 p.1.1‖*‖a.2 p‖)*‖b.1 p.1.2‖ := by
              exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤
            (M^2*δ)*‖a.2 p‖*‖b.1 p.1.2‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hval p.1.1) (norm_nonneg _)) (norm_nonneg _)
        _ ≤ (M^2*δ)*R*‖b.1 p.1.2‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (ha2Point p)
              (mul_nonneg (sq_nonneg M) hδ)) (norm_nonneg _)
        _ ≤ (M^2*δ)*R*M :=
          mul_le_mul_of_nonneg_left (hbPoint p.1.2)
            (mul_nonneg (mul_nonneg (sq_nonneg M) hδ) hR)
        _ = M^3*R*δ := by ring
    have hY : ‖Y‖ ≤ M^2*δ := by
      dsimp [Y]
      calc
        ‖d.1 p.1.1*(a.2 p-c.2 p)*b.1 p.1.2‖ ≤
            ‖d.1 p.1.1‖*‖a.2 p-c.2 p‖*‖b.1 p.1.2‖ := by
          calc
            ‖d.1 p.1.1*(a.2 p-c.2 p)*b.1 p.1.2‖ ≤
                ‖d.1 p.1.1*(a.2 p-c.2 p)‖*‖b.1 p.1.2‖ := norm_mul_le _ _
            _ ≤ (‖d.1 p.1.1‖*‖a.2 p-c.2 p‖)*‖b.1 p.1.2‖ := by
              exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤
            M*‖a.2 p-c.2 p‖*‖b.1 p.1.2‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hdPoint p.1.1) (norm_nonneg _)) (norm_nonneg _)
        _ ≤ M*δ*‖b.1 p.1.2‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (harg2 p) hM) (norm_nonneg _)
        _ ≤ M*δ*M := mul_le_mul_of_nonneg_left (hbPoint p.1.2)
          (mul_nonneg hM hδ)
        _ = M^2*δ := by ring
    have hZ : ‖Z‖ ≤ M^3*R*δ := by
      dsimp [Z]
      calc
        ‖d.1 p.1.1*c.2 p*(b.1 p.1.2-d.1 p.1.2)‖ ≤
            ‖d.1 p.1.1‖*‖c.2 p‖*‖b.1 p.1.2-d.1 p.1.2‖ := by
          calc
            ‖d.1 p.1.1*c.2 p*(b.1 p.1.2-d.1 p.1.2)‖ ≤
                ‖d.1 p.1.1*c.2 p‖*‖b.1 p.1.2-d.1 p.1.2‖ := norm_mul_le _ _
            _ ≤ (‖d.1 p.1.1‖*‖c.2 p‖)*‖b.1 p.1.2-d.1 p.1.2‖ := by
              exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤
            M*‖c.2 p‖*‖b.1 p.1.2-d.1 p.1.2‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hdPoint p.1.1) (norm_nonneg _)) (norm_nonneg _)
        _ ≤ M*R*‖b.1 p.1.2-d.1 p.1.2‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hc2Point p) hM) (norm_nonneg _)
        _ ≤ M*R*(M^2*δ) := mul_le_mul_of_nonneg_left (hval p.1.2)
          (mul_nonneg hM hR)
        _ = M^3*R*δ := by ring
    change ‖b.2 p-d.2 p‖ ≤ K*δ
    rw [hdecomp p]
    calc
      ‖X+Y+Z‖ ≤ ‖X‖+‖Y‖+‖Z‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ M^3*R*δ+M^2*δ+M^3*R*δ := add_le_add (add_le_add hX hY) hZ
      _ = K*δ := by dsimp [K]; ring
  have hfirstField : ‖(b-d).1‖ ≤ M^2*δ := by
    apply (BoundedContinuousFunction.norm_le
      (f := (b-d).1) (mul_nonneg (sq_nonneg M) hδ)).2
    intro p
    simpa using hval p
  have hsecondField : ‖(b-d).2‖ ≤ K*δ := by
    apply (BoundedContinuousFunction.norm_le
      (f := (b-d).2) (mul_nonneg hK hδ)).2
    intro p
    simpa using hderivPoint p
  change ‖b-d‖ ≤ K*δ
  rw [Prod.norm_def]
  exact max_le (hfirstField.trans (mul_le_mul_of_nonneg_right hM2K hδ)) hsecondField
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphInverseLipschitz
