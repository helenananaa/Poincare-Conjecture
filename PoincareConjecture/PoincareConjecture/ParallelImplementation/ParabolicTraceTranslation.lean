import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.AffineRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient
import PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicTraceTranslation
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance standardGroup0 : NormedAddCommGroup (E3 →L[ℝ] E3) := inferInstance
local instance standardSpace0 : NormedSpace ℝ (E3 →L[ℝ] E3) := inferInstance
local instance standardGroup1 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance standardSpace1 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance standardGroup2 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace2 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup3 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace3 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup4 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace4 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup5 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace5 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
theorem translate_zero_trace_correction
    (T alpha : ℝ) (hT : 0 ≤ T) (s z : FullJet T)
    (hsSpace : s.1.1 ∈ parabolicC2HolderSet T alpha)
    (hsTime : (s.1.1.1.1,s.1.2) ∈ slabTimeDerivativeGraph T)
    (hsInc : ∀ p : Pair T, s.2 p=(parabolicRho p.1.1 p.1.2^alpha)⁻¹ •
      (s.1.2 p.1.1-s.1.2 p.1.2))
    (hz : z ∈ fullParabolicJetSet T alpha hT) :

    (s+z).1.1 ∈ parabolicC2HolderSet T alpha ∧
    ((s+z).1.1.1.1,(s+z).1.2) ∈ slabTimeDerivativeGraph T ∧
    (∀ p : Pair T, (s+z).2 p=(parabolicRho p.1.1 p.1.2^alpha)⁻¹ •
      ((s+z).1.2 p.1.1-(s+z).1.2 p.1.2)) ∧
    (∀ x : E3, (s+z).1.1.1.1 (⟨0,le_rfl,hT⟩,x)=s.1.1.1.1 (⟨0,le_rfl,hT⟩,x)) ∧
    ‖s+z‖ ≤ ‖s‖+‖z‖ :=
/- SWARM_PROOF_BEGIN -/
by
  rcases hz with ⟨hzSpace, hzTime, hzInc, hzZero⟩
  constructor
  · change (s.1.1 + z.1.1) ∈ parabolicC2HolderSet T alpha
    change (s.1.1.1 + z.1.1.1) ∈ spaceTimeC2JetSet T ∧
      ∀ p : Pair T,
        (s.1.1.2 + z.1.1.2) p =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            ((s.1.1.1.2.2 + z.1.1.1.2.2) p.1.1 -
              (s.1.1.1.2.2 + z.1.1.1.2.2) p.1.2)
    constructor
    · change ∀ t : Set.Icc (0 : ℝ) T,
        (∀ x : E3,
          HasFDerivAt (fun y => (s.1.1.1.1 + z.1.1.1.1) (t,y))
            ((s.1.1.1.2.1 + z.1.1.1.2.1) (t,x)) x) ∧
        (∀ x : E3,
          HasFDerivAt (fun y => (s.1.1.1.2.1 + z.1.1.1.2.1) (t,y))
            ((s.1.1.1.2.2 + z.1.1.1.2.2) (t,x)) x)
      intro t
      constructor
      · intro x
        have hs := hsSpace.1 t |>.1 x
        have hz' := hzSpace.1 t |>.1 x
        exact hs.add hz'
      · intro x
        have hs := hsSpace.1 t |>.2 x
        have hz' := hzSpace.1 t |>.2 x
        exact hs.add hz'
    · intro p
      have hs := hsSpace.2 p
      have hz' := hzSpace.2 p
      change s.1.1.2 p + z.1.1.2 p = _
      rw [hs, hz']
      rw [← smul_add]
      congr 1
      change (s.1.1.1.2.2 p.1.1 - s.1.1.1.2.2 p.1.2) +
          (z.1.1.1.2.2 p.1.1 - z.1.1.1.2.2 p.1.2) =
        (s.1.1.1.2.2 p.1.1 + z.1.1.1.2.2 p.1.1) -
          (s.1.1.1.2.2 p.1.2 + z.1.1.1.2.2 p.1.2)
      abel
  constructor
  · change (s.1.1.1.1 + z.1.1.1.1, s.1.2 + z.1.2) ∈
      slabTimeDerivativeGraph T
    intro t ht0 htT x
    have hfun : timeExtension (s.1.1.1.1 + z.1.1.1.1) x =
        timeExtension s.1.1.1.1 x + timeExtension z.1.1.1.1 x := by
      funext r
      by_cases hr : r ∈ Set.Icc (0 : ℝ) T
      · simp [timeExtension, hr]
      · simp [timeExtension, hr]
    have hs := hsTime t ht0 htT x
    have hz' := hzTime t ht0 htT x
    have hsum := hs.add hz'
    have hvalue : (s.1.2 + z.1.2) (t,x) = s.1.2 (t,x) + z.1.2 (t,x) := rfl
    rw [hfun, hvalue]
    exact hsum
  constructor
  · intro p
    have hs := hsInc p
    have hz' := hzInc p
    change s.2 p + z.2 p = _
    rw [hs, hz']
    rw [← smul_add]
    congr 1
    change (s.1.2 p.1.1 - s.1.2 p.1.2) +
        (z.1.2 p.1.1 - z.1.2 p.1.2) =
      (s.1.2 p.1.1 + z.1.2 p.1.1) -
        (s.1.2 p.1.2 + z.1.2 p.1.2)
    abel
  constructor
  · intro x
    change s.1.1.1.1 (⟨0, le_rfl, hT⟩, x) +
        z.1.1.1.1 (⟨0, le_rfl, hT⟩, x) = _
    rw [hzZero x]
    simp
  · exact norm_add_le s z
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicTraceTranslation
