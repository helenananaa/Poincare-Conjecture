import PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse
import PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity
import PoincareConjecture.ParallelImplementation.ZeroTraceOperatorValueProjection
import PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection
import PoincareConjecture.ParallelImplementation.FullJetHessianProjection
import PoincareConjecture.ParallelImplementation.FullJetHeatOperator
import PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing
import PoincareConjecture.ParallelImplementation.ParabolicTraceTranslation
import PoincareConjecture.ParallelImplementation.InitialBackgroundSmallness
import PoincareConjecture.ParallelImplementation.BoundedInitialDataJetExtension
import PoincareConjecture.ParallelImplementation.CoupledAffineParabolicFixedPoint
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.AffineRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient
import PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmallInitialRationalHeatSolution
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
theorem exists_small_initial_rational_heat_solution
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (B : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ]
      (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) :
    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i =
        ∑ j : Fin 3, MorganTianLib.MetricCoefficient.symmetricSixMatrix q i j*v j) ∧
      ∃ epsilon delta C : ℝ, 0 < epsilon ∧ 0 < delta ∧ delta ≤ 1 ∧ 0 < C ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ delta →
        ∀ (u0 : E3 →ᵇ E6) (A0 : E3 →ᵇ (E3 →L[ℝ] E6))
          (H0 : E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6)),
          (∀ x : E3, HasFDerivAt u0 (A0 x) x) →
          (∀ x : E3, HasFDerivAt A0 (H0 x) x) →
          ‖u0‖ ≤ epsilon → ‖A0‖ ≤ epsilon → ‖H0‖ ≤ epsilon →
          (∀ x y : E3, ‖u0 x-u0 y‖ ≤ epsilon*‖x-y‖^alpha) →
          (∀ x y : E3, ‖A0 x-A0 y‖ ≤ epsilon*‖x-y‖^alpha) →
          (∀ x y : E3, ‖H0 x-H0 y‖ ≤ epsilon*‖x-y‖^alpha) →
          ∀ F : ForcingJet E6 T, F ∈ forcingGraph E6 T alpha → ‖F‖ ≤ 1 →
          ∃ z : FullJet T, z.1.1 ∈ parabolicC2HolderSet T alpha ∧
            (z.1.1.1.1,z.1.2) ∈ slabTimeDerivativeGraph T ∧
            (∀ p : Pair T, z.2 p=(parabolicRho p.1.1 p.1.2^alpha)⁻¹ •
              (z.1.2 p.1.1-z.1.2 p.1.2)) ∧
            ‖z‖ ≤ C ∧ (∀ x : E3, z.1.1.1.1 (⟨0,le_rfl,hT.le⟩,x)=u0 x) ∧
            ∃ b : ForcingJet (E3 →L[ℝ] E3) T, b ∈ forcingGraph (E3 →L[ℝ] E3) T alpha ∧
              ∀ p : Slab T, ((1+E (z.1.1.1.1 p))*b.1 p=1 ∧ b.1 p*(1+E (z.1.1.1.1 p))=1) ∧
                (∀ v : E3, (1/2:ℝ)*‖v‖^2 ≤ inner ℝ ((1+E (z.1.1.1.1 p)) v) v) ∧
                z.1.2 p-(∑ i : Fin 3, z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
                  F.1 p+(∑ i : Fin 3, ∑ j : Fin 3, ((b.1 p-1) (EuclideanSpace.single j 1)) i •
                    z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
                    B (b.1 p) (b.1 p) (z.1.1.1.2.1 p) (z.1.1.1.2.1 p) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have scalar_control
      (a v h pn qn hn eps p q R W f : ℝ)
      (ha0 : 0 ≤ a) (hv0 : 0 ≤ v) (hh0 : 0 ≤ h) (hpn0 : 0 ≤ pn)
      (hqn0 : 0 ≤ qn) (hhn0 : 0 ≤ hn) (heps0 : 0 ≤ eps) (hp0 : 0 ≤ p)
      (hq0 : 0 ≤ q) (hR0 : 0 ≤ R) (hW0 : 0 ≤ W)
      (ha : a ≤ eps) (hv : v ≤ eps) (hh : h ≤ eps)
      (hpn : pn ≤ p) (hqn : qn ≤ q) (hhn : hn ≤ 1) (hf : f ≤ 1+3*eps) :
      let k := 18*(12*pn*(h+hn*R)+(4*a+12*pn*R)*hn)+
        384*W*pn*(v+qn*R)^2+64*W*qn*(v+qn*R)
      let c := 72*eps+216*p*eps+432*p*R+
        384*W*p*(eps+q*R)^2+64*W*q*(eps+q*R)
      0 ≤ k ∧ k ≤ c ∧
        f+72*a*h+32*W*v^2+k*R ≤ 1+3*eps+(72+32*W)*eps^2+c*R := by
    dsimp only
    have hk : 18*(12*pn*(h+hn*R)+(4*a+12*pn*R)*hn)+
        384*W*pn*(v+qn*R)^2+64*W*qn*(v+qn*R) ≤
        72*eps+216*p*eps+432*p*R+384*W*p*(eps+q*R)^2+64*W*q*(eps+q*R) := by
      calc
        _ ≤ 18*(12*p*(eps+1*R)+(4*eps+12*p*R)*1)+
            384*W*p*(eps+q*R)^2+64*W*q*(eps+q*R) := by gcongr
        _ = _ := by ring
    refine ⟨by positivity, hk, ?_⟩
    calc
      _ ≤ (1+3*eps)+72*eps*eps+32*W*eps^2+
          (72*eps+216*p*eps+432*p*R+384*W*p*(eps+q*R)^2+64*W*q*(eps+q*R))*R := by gcongr
      _ = _ := by ring
  obtain ⟨E, hEinj, hEnorm, hEaction, _⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity.zero_trace_metric_positivity
  obtain ⟨C₀, hC₀, hHeat⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse.exists_parabolic_heat_right_inverse
      alpha ha ha1
  let R : ℝ := 4 * C₀
  let W : ℝ := ‖B‖
  obtain ⟨epsilonBG, delta, hepsilonBG, hepsilonBG1, hdelta, hdelta1, hsmall⟩ :=
    PoincareConjecture.ParallelImplementation.InitialBackgroundSmallness.exists_background_and_time_bounds
      alpha C₀ W ha ha1 hC₀ (by dsimp [W]; positivity)
  let epsilonInit : ℝ := epsilonBG / 3
  let C : ℝ := R + epsilonInit
  have hR : 0 < R := by dsimp [R]; positivity
  have hepsilonInit : 0 < epsilonInit := by dsimp [epsilonInit]; positivity
  have hepsilonInitNonneg : 0 ≤ epsilonInit := hepsilonInit.le
  have hepsilonInitBG : epsilonInit ≤ epsilonBG := by
    dsimp [epsilonInit]
    linarith only [hepsilonBG]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨E, hEinj, hEnorm, hEaction, epsilonInit, delta, C,
    hepsilonInit, hdelta, hdelta1, hC, ?_⟩
  intro T hT hTdelta u0 A0 H0 hu0 hA0 hu0norm hA0norm hH0norm
    hu0holder hA0holder hH0holder F hFgraph hFnorm
  have hT1 : T ≤ 1 := le_trans hTdelta hdelta1
  obtain ⟨X, Y, hX, hY, hXcomplete, hYcomplete, L, D, hLnorm, hDnorm, hLD, hLvalue⟩ :=
    hHeat T hT hT1
  letI : NormedAddCommGroup (FullJet T) := inferInstance
  letI : NormedSpace ℝ (FullJet T) := inferInstance
  letI : NormedAddCommGroup (ForcingJet E6 T) := inferInstance
  letI : NormedSpace ℝ (ForcingJet E6 T) := inferInstance
  letI : NormedAddCommGroup Y := inferInstance
  letI : NormedSpace ℝ Y := inferInstance
  letI : NormedAddCommGroup X := inferInstance
  letI : NormedSpace ℝ X := inferInstance
  letI : CompleteSpace Y := hYcomplete

  obtain ⟨Fu, hFuGraph, hFuValue, hFuBound⟩ :=
    PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing.exists_stationary_parabolic_forcing
      T alpha epsilonInit ha hepsilonInitNonneg u0 hu0holder
  obtain ⟨v0, hv0Graph, hv0Value, hv0Bound⟩ :=
    PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing.exists_stationary_parabolic_forcing
      T alpha epsilonInit ha hepsilonInitNonneg A0 hA0holder
  obtain ⟨Hbg, hHbgGraph, hHbgValue, hHbgBound⟩ :=
    PoincareConjecture.ParallelImplementation.SpatialHolderToParabolicForcing.exists_stationary_parabolic_forcing
      T alpha epsilonInit ha hepsilonInitNonneg H0 hH0holder
  have hFuNorm : ‖Fu‖ ≤ epsilonInit := by
    exact hFuBound.trans (max_le hu0norm le_rfl)
  have hv0Norm : ‖v0‖ ≤ epsilonInit := by
    exact hv0Bound.trans (max_le hA0norm le_rfl)
  have hHbgNorm : ‖Hbg‖ ≤ epsilonInit := by
    exact hHbgBound.trans (max_le hH0norm le_rfl)
  have hFuGraph' : Fu ∈ forcingGraph E6 T alpha := hFuGraph
  obtain ⟨s, hsSpace, hsTime, hsInc, hsData, hsInitial, hsBound⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedInitialDataJetExtension.exists_bounded_initial_jet_extension
      T alpha epsilonInit hT.le ha hepsilonInitNonneg u0 A0 H0 hu0 hA0 hH0holder
  have hsNorm : ‖s‖ ≤ epsilonInit := by
    apply hsBound.trans
    exact max_le hu0norm (max_le hA0norm (max_le hH0norm le_rfl))
  have hHbgSpatial (p : Slab T) : Hbg.1 p = s.1.1.1.2.2 p := by
    calc
      Hbg.1 p = H0 p.2 := hHbgValue p
      _ = s.1.1.1.2.2 p := (hsData p).2.2.1.symm
  have hv0Spatial (p : Slab T) : v0.1 p = s.1.1.1.2.1 p := by
    calc
      v0.1 p = A0 p.2 := hv0Value p
      _ = s.1.1.1.2.1 p := (hsData p).2.1.symm

  let e (i : Fin 3) : E3 := EuclideanSpace.single i 1
  let tr : (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6 :=
    ∑ i : Fin 3, (ContinuousLinearMap.apply ℝ E6 (e i)).comp
      (ContinuousLinearMap.apply ℝ (E3 →L[ℝ] E6) (e i))
  have htr (G : E3 →L[ℝ] E3 →L[ℝ] E6) : ‖tr G‖ ≤ 3 * ‖G‖ := by
    change ‖∑ i : Fin 3, G (e i) (e i)‖ ≤ _
    calc
      _ ≤ ∑ i : Fin 3, ‖G (e i) (e i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, ‖G‖ := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          ‖G (e i) (e i)‖ ≤ ‖G (e i)‖ * ‖e i‖ := (G (e i)).le_opNorm _
          _ ≤ (‖G‖ * ‖e i‖) * ‖e i‖ :=
            mul_le_mul_of_nonneg_right (G.le_opNorm _) (norm_nonneg _)
          _ = ‖G‖ := by simp [e]
      _ = _ := by simp
  have htrNorm : ‖tr‖ ≤ 3 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro G
    exact htr G
  obtain ⟨traceH, htraceHNorm, htraceHValue, htraceHInc, htraceHGraph⟩ :=
    PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift.exists_forcing_graph_linear_lift
      tr T alpha
  have htraceHNorm3 : ‖traceH‖ ≤ 3 := htraceHNorm.trans htrNorm
  have htraceHbgGraph : traceH Hbg ∈ forcingGraph E6 T alpha :=
    htraceHGraph Hbg hHbgGraph
  have htraceBackground (p : Slab T) :
      (traceH Hbg).1 p = ∑ i : Fin 3, s.1.1.1.2.2 p (e i) (e i) := by
    rw [htraceHValue Hbg p]
    simp [tr, e, hHbgSpatial]
  have htraceBackgroundNorm : ‖traceH Hbg‖ ≤ 3 * epsilonBG := by
    calc
      ‖traceH Hbg‖ ≤ ‖traceH‖ * ‖Hbg‖ := traceH.le_opNorm _
      _ ≤ 3 * ‖Hbg‖ :=
        mul_le_mul_of_nonneg_right htraceHNorm3 (norm_nonneg _)
      _ ≤ 3 * epsilonBG := by
        exact mul_le_mul_of_nonneg_left
          (hHbgNorm.trans hepsilonInitBG) (by norm_num)

  let LiftE : ForcingJet E6 T →L[ℝ] ForcingJet (E3 →L[ℝ] E3) T :=
    Classical.choose
      (PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift.exists_forcing_graph_linear_lift
        (-E) T alpha)
  have hLiftEProps :=
    Classical.choose_spec
      (PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift.exists_forcing_graph_linear_lift
        (-E) T alpha)
  have hLiftENorm : ‖LiftE‖ ≤ 3 := by
    have hle := hLiftEProps.1
    exact hle.trans (by simpa using hEnorm)
  have hLiftEValue (g : ForcingJet E6 T) (p : Slab T) :
      (LiftE g).1 p = -E (g.1 p) := by
    exact hLiftEProps.2.1 g p
  have hLiftEGraph (g : ForcingJet E6 T) (hg : g ∈ forcingGraph E6 T alpha) :
      LiftE g ∈ forcingGraph (E3 →L[ℝ] E3) T alpha := by
    exact hLiftEProps.2.2.2 g hg
  let a : ForcingJet (E3 →L[ℝ] E3) T := LiftE Fu
  have haGraph : a ∈ forcingGraph (E3 →L[ℝ] E3) T alpha :=
    hLiftEGraph Fu hFuGraph
  have haNorm : ‖a‖ ≤ epsilonBG := by
    calc
      ‖a‖ ≤ ‖LiftE‖ * ‖Fu‖ := LiftE.le_opNorm _
      _ ≤ 3 * ‖Fu‖ :=
        mul_le_mul_of_nonneg_right hLiftENorm (norm_nonneg _)
      _ ≤ 3 * epsilonInit := mul_le_mul_of_nonneg_left hFuNorm (by norm_num)
      _ = epsilonBG := by dsimp [epsilonInit]; ring
  have haValue (p : Slab T) : a.1 p = -E (s.1.1.1.1 p) := by
    rw [hLiftEValue Fu p, hFuValue p, (hsData p).1]

  obtain ⟨P, hPnorm, hPvalue, hPgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceOperatorValueProjection.exists_zero_trace_operator_value_projection
      T alpha hT ha ha1 Y hY E
  obtain ⟨Q, hQnorm, hQvalue, hQgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection.exists_zero_trace_gradient_projection
      T alpha hT ha ha1 Y hY
  obtain ⟨Hfull, hHfullNorm, hHfullValue, hHincrement, hHfullGraph⟩ :=
    PoincareConjecture.ParallelImplementation.FullJetHessianProjection.exists_full_jet_hessian_projection
      T alpha hT.le
  let Hproj : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T := Hfull.comp Y.subtypeL
  have hHnorm : ‖Hproj‖ ≤ 1 := by
    calc
      ‖Hproj‖ ≤ ‖Hfull‖ * ‖Y.subtypeL‖ := Hfull.opNorm_comp_le _
      _ ≤ 1*1 := mul_le_mul hHfullNorm (Submodule.norm_subtypeL_le Y)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hHvalue (y : Y) (p : Slab T) : (Hproj y).1 p = y.1.1.1.1.2.2 p :=
    hHfullValue y.1 p
  have hyFull (y : Y) : y.1 ∈ fullParabolicJetSet T alpha hT.le := by
    rw [← hY]
    exact y.2
  have hHgraph' (y : Y) : Hproj y ∈ forcingGraph
      (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha := hHfullGraph y.1 (hyFull y)
  let tau : ℝ := T + 8 * T ^ (1 - alpha / 2)
  let pSmall : ℝ := 3 * tau
  let qSmall : ℝ := 3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)
  let Kbg : ℝ := 72 * epsilonBG + 216 * pSmall * epsilonBG +
    432 * pSmall * R + 384 * W * pSmall * (epsilonBG + qSmall * R) ^ 2 +
    64 * W * qSmall * (epsilonBG + qSmall * R)
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hpSmall : 0 ≤ pSmall := by dsimp [pSmall]; positivity
  have hqSmall : 0 ≤ qSmall := by dsimp [qSmall]; positivity
  have hKbg : 0 ≤ Kbg := by dsimp [Kbg, W]; positivity
  have hsmallT := hsmall T hT hTdelta
  have hsmallProjection : epsilonBG + pSmall * R ≤ 1 / 2 := by
    simpa [R, tau, pSmall] using hsmallT.1
  have hsmallLip : C₀ * Kbg ≤ 1 / 2 := by
    simpa only [R, tau, pSmall, qSmall, Kbg] using hsmallT.2.1
  have hsmallSelf : C₀ *
      (1 + 3 * epsilonBG + (72 + 32 * W) * epsilonBG ^ 2 + Kbg * R) ≤ R := by
    simpa only [R, tau, pSmall, qSmall, Kbg] using hsmallT.2.2
  have hPnormSmall : ‖P‖ ≤ pSmall := by
    calc
      ‖P‖ ≤ ‖E‖ * tau := by simpa [tau] using hPnorm
      _ ≤ 3 * tau := mul_le_mul_of_nonneg_right hEnorm htau
      _ = pSmall := rfl
  have hQnormSmall : ‖Q‖ ≤ qSmall := by
    simpa [qSmall] using hQnorm

  let f : X := ⟨F + traceH Hbg,
    X.add_mem
      ((congrArg (fun S : Set (ForcingJet E6 T) => F ∈ S) hX).mpr hFgraph)
      ((congrArg (fun S : Set (ForcingJet E6 T) => traceH Hbg ∈ S) hX).mpr
        htraceHbgGraph)⟩
  have hfNorm : ‖f‖ ≤ 1 + 3 * epsilonBG := by
    change ‖F + traceH Hbg‖ ≤ _
    calc
      ‖F + traceH Hbg‖ ≤ ‖F‖ + ‖traceH Hbg‖ := norm_add_le _ _
      _ ≤ 1 + 3 * epsilonBG := add_le_add hFnorm htraceBackgroundNorm

  have hsmallCoupled : ‖a‖ + ‖P‖ * R ≤ 1 / 2 := by
    calc
      ‖a‖ + ‖P‖ * R ≤ epsilonBG + pSmall * R :=
        add_le_add haNorm (mul_le_mul_of_nonneg_right hPnormSmall hR.le)
      _ ≤ 1 / 2 := hsmallProjection
  let Kact : ℝ :=
    18 * (12 * ‖P‖ * (‖Hbg‖ + ‖Hproj‖ * R) +
      (4 * ‖a‖ + 12 * ‖P‖ * R) * ‖Hproj‖) +
      384 * W * ‖P‖ * (‖v0‖ + ‖Q‖ * R) ^ 2 +
      64 * W * ‖Q‖ * (‖v0‖ + ‖Q‖ * R)
  have hControl := scalar_control ‖a‖ ‖v0‖ ‖Hbg‖ ‖P‖ ‖Q‖ ‖Hproj‖
    epsilonBG pSmall qSmall R W ‖f‖
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hepsilonBG.le hpSmall hqSmall hR.le
    (by dsimp [W]; positivity) haNorm (hv0Norm.trans hepsilonInitBG)
    (hHbgNorm.trans hepsilonInitBG) hPnormSmall hQnormSmall hHnorm hfNorm
  have hKactNonneg : 0 ≤ Kact := hControl.1
  have hKact : Kact ≤ Kbg := hControl.2.1
  have hDcontract : ‖D‖ * Kact < 1 :=
    lt_of_le_of_lt (le_trans
      (mul_le_mul hDnorm hKact hKactNonneg hC₀.le) hsmallLip) (by norm_num)
  have hself : ‖D‖*(‖f‖+72*‖a‖*‖Hbg‖+32*W*‖v0‖^2+Kact*R) ≤ R := by
    calc
      _ ≤ C₀*(‖f‖+72*‖a‖*‖Hbg‖+32*W*‖v0‖^2+Kact*R) :=
        mul_le_mul_of_nonneg_right hDnorm (by positivity)
      _ ≤ C₀*(1+3*epsilonBG+(72+32*W)*epsilonBG^2+Kbg*R) :=
        mul_le_mul_of_nonneg_left hControl.2.2 hC₀.le
      _ ≤ R := hsmallSelf
  obtain ⟨y, hy, b, hbgraph, hbNorm, hbData⟩ :=
    PoincareConjecture.ParallelImplementation.CoupledAffineParabolicFixedPoint.exists_coupled_affine_operator_solution
      T alpha R hR X hX L D hLD f B a v0 Hbg haGraph hv0Graph hHbgGraph
      P Q Hproj hPgraph hQgraph hHgraph' hsmallCoupled hself hDcontract
  have hbInverse (p : Slab T) := (hbData p).1
  have hCoupled (p : Slab T) := (hbData p).2
  let z : FullJet T := s + y.1
  have hyFullSet : y.1 ∈ fullParabolicJetSet T alpha hT.le := hyFull y
  have hyNorm : ‖y.1‖ ≤ R := by simpa using hy
  have hsNormalizedInc (p : Pair T) : s.2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ • (s.1.2 p.1.1 - s.1.2 p.1.2) := by
    rw [hsInc p, (hsData p.1.1).2.2.2, (hsData p.1.2).2.2.2]
    simp
  have htranslated :=
    PoincareConjecture.ParallelImplementation.ParabolicTraceTranslation.translate_zero_trace_correction
      T alpha hT.le s y.1 hsSpace hsTime hsNormalizedInc hyFullSet
  have hzSpace : z.1.1 ∈ parabolicC2HolderSet T alpha := by
    simpa [z] using htranslated.1
  have hzTime : (z.1.1.1.1, z.1.2) ∈ slabTimeDerivativeGraph T := by
    simpa [z] using htranslated.2.1
  have hzInc : ∀ p : Pair T, z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (z.1.2 p.1.1-z.1.2 p.1.2) := by
    simpa [z] using htranslated.2.2.1
  have hzInitial (x : E3) : z.1.1.1.1 (⟨0, le_rfl, hT.le⟩, x) = u0 x := by
    calc
      z.1.1.1.1 (⟨0, le_rfl, hT.le⟩, x) =
          s.1.1.1.1 (⟨0, le_rfl, hT.le⟩, x) := by
            simpa [z] using htranslated.2.2.2.1 x
      _ = u0 x := hsInitial x
  have hzNorm : ‖z‖ ≤ C := by
    calc
      ‖z‖ ≤ ‖s‖ + ‖y.1‖ := by simpa [z] using htranslated.2.2.2.2
      _ ≤ epsilonInit + R := add_le_add hsNorm hyNorm
      _ = C := by dsimp [C]; ring

  have haPyValue (p : Slab T) : (a + P y).1 p = -E (z.1.1.1.1 p) := by
    change a.1 p + (P y).1 p = -E (z.1.1.1.1 p)
    rw [haValue p, hPvalue y p]
    change -E (s.1.1.1.1 p) + -E (y.1.1.1.1.1 p) =
      -E (s.1.1.1.1 p + y.1.1.1.1.1 p)
    rw [map_add]
    abel
  have hsmallAP : ‖a + P y‖ ≤ 1 / 2 := by
    calc
      ‖a + P y‖ ≤ ‖a‖ + ‖P y‖ := norm_add_le _ _
      _ ≤ epsilonBG + ‖P‖ * ‖y‖ :=
        add_le_add haNorm (P.le_opNorm y)
      _ ≤ epsilonBG + pSmall * R :=
        add_le_add le_rfl (mul_le_mul hPnormSmall hy (norm_nonneg y) hpSmall)
      _ ≤ 1 / 2 := hsmallProjection
  have hsmallAPvalue (p : Slab T) : ‖(a + P y).1 p‖ ≤ 1 / 2 := by
    calc
      ‖(a + P y).1 p‖ ≤ ‖(a + P y).1‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ ‖a + P y‖ := norm_fst_le _
      _ ≤ 1 / 2 := hsmallAP
  have hEsmall (p : Slab T) : ‖E (z.1.1.1.1 p)‖ ≤ (1 / 2 : ℝ) := by
    have h := hsmallAPvalue p
    rw [haPyValue p, norm_neg] at h
    exact h
  have hcoeff (p : Slab T) : 1 - (a + P y).1 p = 1 + E (z.1.1.1.1 p) := by
    rw [haPyValue p]
    simp
  have hcoercive (p : Slab T) (v : E3) :
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ ((1 + E (z.1.1.1.1 p)) v) v := by
    let A := E (z.1.1.1.1 p)
    have hAv : ‖A v‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
      calc
        ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
        _ ≤ (1 / 2 : ℝ) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (by simpa [A] using hEsmall p) (norm_nonneg v)
    have habs : |inner ℝ (A v) v| ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
      calc
        |inner ℝ (A v) v| ≤ ‖A v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ ((1 / 2 : ℝ) * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hAv (norm_nonneg v)
        _ = (1 / 2 : ℝ) * ‖v‖ ^ 2 := by ring
    have hmetric : inner ℝ ((1 + A) v) v = ‖v‖ ^ 2 + inner ℝ (A v) v := by
      rw [show (1 + A) v = v + A v by simp, inner_add_left, real_inner_self_eq_norm_sq]
    have hperturb : -(1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ (A v) v := by
      calc
        -(1 / 2 : ℝ) * ‖v‖ ^ 2 = -((1 / 2 : ℝ) * ‖v‖ ^ 2) := by ring
        _ ≤ inner ℝ (A v) v := neg_le_of_abs_le habs
    rw [show E (z.1.1.1.1 p) = A by rfl, hmetric]
    linarith only [hperturb]

  have hHessianSum (p : Slab T) :
      (∑ i : Fin 3, z.1.1.1.2.2 p (e i) (e i)) =
        (∑ i : Fin 3, s.1.1.1.2.2 p (e i) (e i)) +
          (∑ i : Fin 3, y.1.1.1.1.2.2 p (e i) (e i)) := by
    change (∑ i : Fin 3,
      (s.1.1.1.2.2 p (e i) (e i) + y.1.1.1.1.2.2 p (e i) (e i))) = _
    rw [Finset.sum_add_distrib]
  have hyHeat (p : Slab T) :
      y.1.1.2 p - (∑ i : Fin 3, y.1.1.1.1.2.2 p (e i) (e i)) =
        F.1 p + (traceH Hbg).1 p +
          (∑ i : Fin 3, ∑ j : Fin 3,
            ((b.1 p - 1) (e j)) i • (Hbg + Hproj y).1 p (e i) (e j)) +
          B (b.1 p) (b.1 p) ((v0 + Q y).1 p) ((v0 + Q y).1 p) := by
    calc
      _ = (L y).1.1 p := (hLvalue y p).symm
      _ = f.1.1 p +
          (∑ i : Fin 3, ∑ j : Fin 3,
            ((b.1 p - 1) (e j)) i • (Hbg + Hproj y).1 p (e i) (e j)) +
          B (b.1 p) (b.1 p) ((v0 + Q y).1 p) ((v0 + Q y).1 p) := hCoupled p
      _ = F.1 p + (traceH Hbg).1 p +
          (∑ i : Fin 3, ∑ j : Fin 3,
            ((b.1 p - 1) (e j)) i • (Hbg + Hproj y).1 p (e i) (e j)) +
          B (b.1 p) (b.1 p) ((v0 + Q y).1 p) ((v0 + Q y).1 p) := by
            rfl
  have hHessianValue (p : Slab T) (v w : E3) :
      (Hbg + Hproj y).1 p v w = z.1.1.1.2.2 p v w := by
    change Hbg.1 p v w + (Hproj y).1 p v w =
      s.1.1.1.2.2 p v w + y.1.1.1.1.2.2 p v w
    rw [hHbgSpatial p, hHvalue y p]
  have hGradientValue (p : Slab T) : (v0 + Q y).1 p = z.1.1.1.2.1 p := by
    change v0.1 p + (Q y).1 p = s.1.1.1.2.1 p + y.1.1.1.1.2.1 p
    rw [hv0Spatial p, hQvalue y p]
  have hNonlinearity (p : Slab T) :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ((b.1 p - 1) (e j)) i • (Hbg + Hproj y).1 p (e i) (e j)) +
        B (b.1 p) (b.1 p) ((v0 + Q y).1 p) ((v0 + Q y).1 p) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        ((b.1 p - 1) (e j)) i • z.1.1.1.2.2 p (e i) (e j)) +
        B (b.1 p) (b.1 p) (z.1.1.1.2.1 p) (z.1.1.1.2.1 p) := by
    simp_rw [hHessianValue p, hGradientValue p]
  have htotalHeat (p : Slab T) :
      (y.1.1.2 p - (∑ i : Fin 3, y.1.1.1.1.2.2 p (e i) (e i))) -
          (traceH Hbg).1 p =
        F.1 p +
          (∑ i : Fin 3, ∑ j : Fin 3,
            ((b.1 p - 1) (e j)) i • (Hbg + Hproj y).1 p (e i) (e j)) +
          B (b.1 p) (b.1 p) ((v0 + Q y).1 p) ((v0 + Q y).1 p) := by
    rw [hyHeat p]
    abel
  refine ⟨z, hzSpace, hzTime, hzInc, hzNorm, hzInitial, b, hbgraph, ?_⟩
  intro p
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [← hcoeff p]
      exact (hbInverse p).1
    · rw [← hcoeff p]
      exact (hbInverse p).2
  refine ⟨?_, ?_⟩
  · exact hcoercive p
  calc
    z.1.2 p - (∑ i : Fin 3, z.1.1.1.2.2 p (e i) (e i)) =
        (y.1.1.2 p - (∑ i : Fin 3, y.1.1.1.1.2.2 p (e i) (e i))) -
          (traceH Hbg).1 p := by
            rw [show z.1.2 p = y.1.1.2 p by
              change s.1.2 p + y.1.1.2 p = y.1.1.2 p
              rw [(hsData p).2.2.2]
              simp, hHessianSum p, htraceBackground p]
            abel
    _ = F.1 p +
          (∑ i : Fin 3, ∑ j : Fin 3,
            ((b.1 p - 1) (e j)) i • (Hbg + Hproj y).1 p (e i) (e j)) +
          B (b.1 p) (b.1 p) ((v0 + Q y).1 p) ((v0 + Q y).1 p) := htotalHeat p
    _ = F.1 p +
          (∑ i : Fin 3, ∑ j : Fin 3,
            ((b.1 p - 1) (e j)) i • z.1.1.1.2.2 p (e i) (e j)) +
          B (b.1 p) (b.1 p) (z.1.1.1.2.1 p) (z.1.1.1.2.1 p) := by
            simpa only [add_assoc] using congrArg (fun q : E6 => F.1 p + q) (hNonlinearity p)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmallInitialRationalHeatSolution
