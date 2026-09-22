import PoincareConjecture.ProofContract.V1.Obligations
import PoincareConjecture.ProofContract.Proofs.CoordinateBallExists
import PoincareConjecture.ProofContract.Proofs.CoordinateClosureFrontier
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A monotone radial compression profile, identity outside radius two. -/
theorem buffered_radius_profile (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ p : ℝ ≃ₜ ℝ, StrictMono p ∧ p 0 = 0 ∧
      (∀ s : ℝ, s ≤ 1 → p s = r*s) ∧ (∀ s : ℝ, 2 ≤ s → p s = s) :=
/- SWARM_PROOF_BEGIN -/
by
  let p : ℝ → ℝ := fun s =>
    if s ≤ 1 then r * s else if s ≤ 2 then r + (2 - r) * (s - 1) else s
  have hp : StrictMono p := by
    intro a b hab
    by_cases ha : a ≤ 1
    · by_cases hb : b ≤ 1
      · simp only [p, if_pos ha, if_pos hb]
        nlinarith [hr]
      · have hb1 : 1 < b := lt_of_not_ge hb
        by_cases hb2 : b ≤ 2
        · rw [show p a = r * a by simp [p, ha],
            show p b = r + (2 - r) * (b - 1) by
              simp [p, not_le_of_gt hb1, hb2]]
          nlinarith [hr, hr1]
        · rw [show p a = r * a by simp [p, ha],
            show p b = b by simp [p, not_le_of_gt hb1, hb2]]
          nlinarith [hr, hr1]
    · have ha1 : 1 < a := lt_of_not_ge ha
      have hb1 : 1 < b := lt_trans ha1 hab
      by_cases ha2 : a ≤ 2
      · by_cases hb2 : b ≤ 2
        · rw [show p a = r + (2 - r) * (a - 1) by simp [p, ha, ha2],
            show p b = r + (2 - r) * (b - 1) by
              simp [p, not_le_of_gt hb1, hb2]]
          nlinarith [hr1]
        · rw [show p a = r + (2 - r) * (a - 1) by simp [p, ha, ha2],
            show p b = b by simp [p, not_le_of_gt hb1, hb2]]
          nlinarith [hr1]
      · have ha2' : 2 < a := lt_of_not_ge ha2
        have hb2 : ¬ b ≤ 2 := by
          intro h
          linarith
        rw [show p a = a by simp [p, ha, ha2],
            show p b = b by simp [p, not_le_of_gt hb1, hb2]]
        exact hab
  let g : ℝ → ℝ := fun y =>
    if y ≤ r then y / r else if y ≤ 2 then 1 + (y - r) / (2 - r) else y
  have hg : Function.RightInverse g p := by
    intro y
    by_cases hy : y ≤ r
    · have hxr : y / r ≤ 1 := (div_le_iff₀ hr).2 (by nlinarith)
      rw [show g y = y / r by simp [g, hy]]
      simp [p, hxr]
      field_simp
    · have hyr : r < y := lt_of_not_ge hy
      by_cases hy2 : y ≤ 2
      · have hden : 0 < 2 - r := by linarith
        have hquotpos : 0 < (y - r) / (2 - r) :=
          div_pos (by linarith) hden
        have hquotle : (y - r) / (2 - r) ≤ 1 :=
          (div_le_iff₀ hden).2 (by linarith)
        have hx1 : 1 < 1 + (y - r) / (2 - r) := by linarith
        have hx2 : 1 + (y - r) / (2 - r) ≤ 2 := by linarith
        rw [show g y = 1 + (y - r) / (2 - r) by simp [g, hy, hy2]]
        simp [p, not_le_of_gt hx1, hx2]
        field_simp
        ring
      · have hy2' : 2 < y := lt_of_not_ge hy2
        rw [show g y = y by simp [g, hy, hy2]]
        have hy1 : 1 < y := by linarith [hr1, hyr]
        simp [p, not_le_of_gt hy1, not_le_of_gt hy2']
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse p hp g hg
  have he : (e.toHomeomorph : ℝ → ℝ) = p := by
    rfl
  refine ⟨e.toHomeomorph, ?_, ?_, ?_, ?_⟩
  · rw [he]
    exact hp
  · rw [he]
    simp [p]
  · intro s hs
    rw [he]
    simp [p, hs]
  · intro s hs
    rw [he]
    have hs1 : ¬ s ≤ 1 := by linarith
    by_cases hs2 : s ≤ 2
    · have hs_eq : s = 2 := le_antisymm hs2 hs
      subst s
      simp [p]
      ring
    · have hs2' : 2 < s := lt_of_not_ge hs2
      simp [p, hs1, not_le_of_gt hs2']
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
