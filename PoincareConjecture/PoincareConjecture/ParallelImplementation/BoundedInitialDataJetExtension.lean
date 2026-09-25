import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.AffineRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient
import PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity
import PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BoundedInitialDataJetExtension
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
theorem exists_bounded_initial_jet_extension
    (T alpha K : ℝ) (hT : 0 ≤ T) (ha : 0 < alpha) (hK : 0 ≤ K)
    (u0 : E3 →ᵇ E6) (A0 : E3 →ᵇ (E3 →L[ℝ] E6))
    (H0 : E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6))
    (hu0 : ∀ x : E3, HasFDerivAt u0 (A0 x) x)
    (hA0 : ∀ x : E3, HasFDerivAt A0 (H0 x) x)
    (hH0 : ∀ x y : E3, ‖H0 x-H0 y‖ ≤ K*‖x-y‖^alpha) :

    ∃ s : FullJet T, s.1.1 ∈ parabolicC2HolderSet T alpha ∧
      (s.1.1.1.1,s.1.2) ∈ slabTimeDerivativeGraph T ∧
      (∀ p : Pair T, s.2 p=0) ∧
      (∀ p : Slab T, s.1.1.1.1 p=u0 p.2 ∧ s.1.1.1.2.1 p=A0 p.2 ∧
        s.1.1.1.2.2 p=H0 p.2 ∧ s.1.2 p=0) ∧
      (∀ x : E3, s.1.1.1.1 (⟨0,le_rfl,hT⟩,x)=u0 x) ∧
      ‖s‖ ≤ max ‖u0‖ (max ‖A0‖ (max ‖H0‖ K)) :=
/- SWARM_PROOF_BEGIN -/
by
  let spatialProjection : ContinuousMap (Slab T) E3 :=
    ⟨fun p => p.2, continuous_snd⟩
  let uField : Slab T →ᵇ E6 := u0.compContinuous spatialProjection
  let aField : Slab T →ᵇ (E3 →L[ℝ] E6) := A0.compContinuous spatialProjection
  let hField : Slab T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6) :=
    H0.compContinuous spatialProjection
  have huValue (p : Slab T) : uField p = u0 p.2 := rfl
  have haValue (p : Slab T) : aField p = A0 p.2 := rfl
  have hhValue (p : Slab T) : hField p = H0 p.2 := rfl
  obtain ⟨F, hFgraph, hFvalue, hFnorm⟩ :=
    PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing.exists_stationary_parabolic_forcing
      T alpha K ha hK H0 hH0
  let j : Jet T := (uField, (aField, hField))
  let q : HolderJet T := (j, F.2)
  let timeZero : Slab T →ᵇ E6 := 0
  let incrementZero : Pair T →ᵇ E6 := 0
  let s : FullJet T := ((q, timeZero), incrementZero)
  have hspace : j ∈ spaceTimeC2JetSet T := by
    intro t
    constructor
    · intro x
      simpa [j, uField, aField, spatialProjection] using hu0 x
    · intro x
      simpa [j, aField, hField, spatialProjection] using hA0 x
  have hholder : q ∈ parabolicC2HolderSet T alpha := by
    change j ∈ spaceTimeC2JetSet T ∧ ∀ p : Pair T,
      F.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (j.2.2 p.1.1 - j.2.2 p.1.2)
    constructor
    · exact hspace
    · intro p
      calc
        F.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            (F.1 p.1.1 - F.1 p.1.2) := hFgraph p
        _ = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            (hField p.1.1 - hField p.1.2) := by
              rw [hFvalue, hhValue, hFvalue, hhValue]
  have htimeGraph :
      (uField, timeZero) ∈ slabTimeDerivativeGraph T := by
    rw [slabTimeDerivativeGraph]
    intro t ht0 htT x
    have hlocal :
        (fun r : ℝ => timeExtension uField x r) =ᶠ[𝓝 (t : ℝ)]
          (fun _ : ℝ => u0 x) := by
      filter_upwards [Ioo_mem_nhds ht0 htT] with r hr
      have hrIcc : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
      simp [timeExtension, hrIcc, uField, spatialProjection]
    have hderiv : HasDerivAt (fun _ : ℝ => u0 x) 0 (t : ℝ) :=
      hasDerivAt_const (𝕜 := ℝ) (x := (t : ℝ)) (c := u0 x)
    have hactual : HasDerivAt (fun r : ℝ => timeExtension uField x r) 0 (t : ℝ) :=
      hderiv.congr_of_eventuallyEq hlocal
    simpa [timeZero] using hactual
  have huNorm : ‖uField‖ ≤ ‖u0‖ :=
    BoundedContinuousFunction.norm_compContinuous_le u0 spatialProjection
  have haNorm : ‖aField‖ ≤ ‖A0‖ :=
    BoundedContinuousFunction.norm_compContinuous_le A0 spatialProjection
  have hhNorm : ‖hField‖ ≤ ‖H0‖ :=
    BoundedContinuousFunction.norm_compContinuous_le H0 spatialProjection
  have hF2Norm : ‖F.2‖ ≤ max ‖H0‖ K := by
    change max ‖F.1‖ ‖F.2‖ ≤ max ‖H0‖ K at hFnorm
    exact (le_max_right ‖F.1‖ ‖F.2‖).trans hFnorm
  refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change q ∈ parabolicC2HolderSet T alpha
    exact hholder
  · change (uField, timeZero) ∈ slabTimeDerivativeGraph T
    exact htimeGraph
  · intro p
    simp [s, incrementZero]
  · intro p
    change uField p = u0 p.2 ∧ aField p = A0 p.2 ∧
      hField p = H0 p.2 ∧ timeZero p = 0
    exact ⟨huValue p, haValue p, hhValue p, by simp [timeZero]⟩
  · intro x
    change uField (⟨0, le_rfl, hT⟩, x) = u0 x
    rfl
  · let M : ℝ := max ‖u0‖ (max ‖A0‖ (max ‖H0‖ K))
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      exact le_trans (norm_nonneg u0) (le_max_left _ _)
    have huM : ‖uField‖ ≤ M :=
      huNorm.trans (by dsimp [M]; exact le_max_left _ _)
    have haM : ‖aField‖ ≤ M := by
      apply haNorm.trans
      dsimp [M]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hhM : ‖hField‖ ≤ M := by
      apply hhNorm.trans
      dsimp [M]
      exact (le_max_left ‖H0‖ K).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hF2M : ‖F.2‖ ≤ M := by
      apply hF2Norm.trans
      dsimp [M]
      exact (le_max_right _ _).trans (le_max_right _ _)
    change ‖((q, timeZero), incrementZero)‖ ≤ M
    simp only [Prod.norm_def]
    apply max_le
    · apply max_le
      · apply max_le
        · apply max_le
          · exact huM
          · exact max_le haM hhM
        · exact hF2M
      · simpa [timeZero] using hM_nonneg
    · simpa [incrementZero] using hM_nonneg
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BoundedInitialDataJetExtension
