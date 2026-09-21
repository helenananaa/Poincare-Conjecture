import Mathlib

open Set MeasureTheory Matrix Function
open scoped ContDiff Manifold Topology ENNReal Bundle BigOperators

noncomputable section
namespace MorganTianLib

/-- **Math.** Replacing finitely many disjoint measured pieces adds their genuine volume losses. -/
theorem finite_volume_loss_of_measurable_replacement
    {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype A]
    (mu : Measure X) (nu : Measure Y) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (old : Option A → Set X) (new : Option A → Set Y) (loss : A → ℝ)
    (holdMeas : ∀ i, MeasurableSet (old i)) (hnewMeas : ∀ i, MeasurableSet (new i))
    (holdDisjoint : Pairwise (Disjoint on old))
    (hnewDisjoint : Pairwise (Disjoint on new))
    (holdCover : (⋃ i, old i) = Set.univ) (hnewCover : (⋃ i, new i) = Set.univ)
    (hcore : (mu (old none)).toReal = (nu (new none)).toReal)
    (hloss : ∀ i, loss i + (nu (new (some i))).toReal ≤ (mu (old (some i))).toReal) :
    (∑ i, loss i) + (nu Set.univ).toReal ≤ (mu Set.univ).toReal := by
/- SWARM_PROOF_BEGIN -/
  have hmuUnion : mu Set.univ = ∑' i : Option A, mu (old i) := by
    rw [← holdCover]
    exact measure_iUnion holdDisjoint holdMeas
  have hnuUnion : nu Set.univ = ∑' i : Option A, nu (new i) := by
    rw [← hnewCover]
    exact measure_iUnion hnewDisjoint hnewMeas
  have hmuReal : (mu Set.univ).toReal = ∑ i : Option A, (mu (old i)).toReal := by
    rw [hmuUnion, ENNReal.tsum_toReal_eq (fun i ↦ measure_ne_top mu (old i))]
    simp
  have hnuReal : (nu Set.univ).toReal = ∑ i : Option A, (nu (new i)).toReal := by
    rw [hnuUnion, ENNReal.tsum_toReal_eq (fun i ↦ measure_ne_top nu (new i))]
    simp
  have hpieces :
      (∑ i : A, loss i) + ∑ i : A, (nu (new (some i))).toReal ≤
        ∑ i : A, (mu (old (some i))).toReal := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hloss i)
    rw [Finset.sum_add_distrib] at h
    exact h
  rw [hmuReal, hnuReal, Fintype.sum_option, Fintype.sum_option]
  linarith
/- SWARM_PROOF_END -/

end MorganTianLib
