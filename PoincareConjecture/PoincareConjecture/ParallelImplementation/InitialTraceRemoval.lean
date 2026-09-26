import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.InitialTraceRemoval
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Removing a compatible initial-trace lift from a classical parabolic jet
produces an actual zero-initial-trace FullJet. This is the reverse affine step
needed before applying the existing zero-trace heat solver. -/
theorem remove_initial_trace_correction
    (T alpha : ℝ) (hT : 0 ≤ T) (q s : FullJet T)
    (hqSpace : q.1.1 ∈ parabolicC2HolderSet T alpha)
    (hqTime : (q.1.1.1.1, q.1.2) ∈ slabTimeDerivativeGraph T)
    (hqTimeInc : ∀ p : Pair T,
      q.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (q.1.2 p.1.1 - q.1.2 p.1.2))
    (hsSpace : s.1.1 ∈ parabolicC2HolderSet T alpha)
    (hsTime : (s.1.1.1.1, s.1.2) ∈ slabTimeDerivativeGraph T)
    (hsTimeInc : ∀ p : Pair T,
      s.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (s.1.2 p.1.1 - s.1.2 p.1.2))
    (htrace : ∀ x : E3,
      q.1.1.1.1 (⟨0, le_rfl, hT⟩, x) =
        s.1.1.1.1 (⟨0, le_rfl, hT⟩, x)) :
    q - s ∈ fullParabolicJetSet T alpha hT :=
/- SWARM_PROOF_BEGIN -/
by
  change (q.1.1 - s.1.1 ∈ parabolicC2HolderSet T alpha) ∧
    ((q.1.1.1.1 - s.1.1.1.1, q.1.2 - s.1.2) ∈
      slabTimeDerivativeGraph T) ∧
    (∀ p : Pair T, q.2 p - s.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((q.1.2 - s.1.2) p.1.1 - (q.1.2 - s.1.2) p.1.2)) ∧
    (∀ x : E3, (q.1.1.1.1 - s.1.1.1.1) (⟨0, le_rfl, hT⟩, x) = 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hqSpace with ⟨hqJet, hqHess⟩
    rcases hsSpace with ⟨hsJet, hsHess⟩
    change (q.1.1.1 - s.1.1.1) ∈ spaceTimeC2JetSet T ∧ _
    constructor
    · intro t
      constructor
      · intro x
        change HasFDerivAt
          (fun y => q.1.1.1.1 (t, y) - s.1.1.1.1 (t, y))
          ((q.1.1.1.2.1 - s.1.1.1.2.1) (t, x)) x
        exact ((hqJet t).1 x).sub ((hsJet t).1 x)
      · intro x
        change HasFDerivAt
          (fun y => q.1.1.1.2.1 (t, y) - s.1.1.1.2.1 (t, y))
          ((q.1.1.1.2.2 - s.1.1.1.2.2) (t, x)) x
        exact ((hqJet t).2 x).sub ((hsJet t).2 x)
    · intro p
      change q.1.1.2 p - s.1.1.2 p =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          ((q.1.1.1.2.2 p.1.1 - s.1.1.1.2.2 p.1.1) -
            (q.1.1.1.2.2 p.1.2 - s.1.1.1.2.2 p.1.2))
      rw [hqHess p, hsHess p, ← smul_sub]
      congr 1
      abel
  · intro t ht0 htT x
    have hfun : timeExtension (q.1.1.1.1 - s.1.1.1.1) x =
        timeExtension q.1.1.1.1 x - timeExtension s.1.1.1.1 x := by
      funext r
      by_cases hr : r ∈ Set.Icc (0 : ℝ) T
      · simp [timeExtension, hr]
      · simp [timeExtension, hr]
    have hq := hqTime t ht0 htT x
    have hs := hsTime t ht0 htT x
    have hsub := hq.sub hs
    rw [hfun]
    simpa [timeExtension, ht0.le, htT.le] using hsub
  · intro p
    change q.2 p - s.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((q.1.2 p.1.1 - s.1.2 p.1.1) -
          (q.1.2 p.1.2 - s.1.2 p.1.2))
    rw [hqTimeInc p, hsTimeInc p, ← smul_sub]
    congr 1
    abel
  · intro x
    change q.1.1.1.1 (⟨0, le_rfl, hT⟩, x) -
        s.1.1.1.1 (⟨0, le_rfl, hT⟩, x) = 0
    rw [htrace x]
    simp
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.InitialTraceRemoval
