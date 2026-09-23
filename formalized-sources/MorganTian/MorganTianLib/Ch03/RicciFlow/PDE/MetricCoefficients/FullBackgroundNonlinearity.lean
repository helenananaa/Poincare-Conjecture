import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BackgroundJetSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.FullDeTurckNonlinearity
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BackgroundConnectionContraction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "JBg" => J3 × (T3 × (Fin 3 → T3))
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
def fullBackgroundNonlinearity (q : JBg) : E9 :=
  WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 =>
    fullDeTurckNonlinearity q.1 ij - backgroundLieCorrection q.1.1 q.1.2 q.2.1 q.2.2 ij.1 ij.2)

/-- **Math.** full background nonlinearity smooth. -/
theorem full_background_nonlinearity_smooth (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3) (T : T3) (R : Fin 3 → T3)
    (c : ℝ) (hc : 0 < c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    ContDiffAt ℝ ∞ fullBackgroundNonlinearity ((A,P),(T,R)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : NormedAddCommGroup E9 := inferInstance
  letI : InnerProductSpace ℝ E9 := inferInstance
  apply contDiffAt_euclidean.mpr
  intro ij
  change ContDiffAt ℝ ∞
    (fun q : JBg =>
      fullDeTurckNonlinearity q.1 ij -
        backgroundLieCorrection q.1.1 q.1.2 q.2.1 q.2.2 ij.1 ij.2)
    ((A, P), (T, R))
  let q₀ : JBg := ((A, P), (T, R))
  have hDet : ContDiffAt ℝ ∞
      (fun q : JBg => fullDeTurckNonlinearity q.1) q₀ := by
    exact ContDiffAt.comp (x := q₀) (f := fun q : JBg => q.1)
      (g := fullDeTurckNonlinearity)
      (full_deturck_nonlinearity_smooth A P c hc hA) contDiffAt_fst
  have hDetCoord : ContDiffAt ℝ ∞
      (fun q : JBg => fullDeTurckNonlinearity q.1 ij) q₀ := by
    simpa [Function.comp_def, EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj (𝕜 := ℝ) ij).contDiff.contDiffAt.comp q₀ hDet)
  have hPair : ContDiffAt ℝ ∞
      (fun q : JBg => (q.1.1, q.2.1)) q₀ := by
    fun_prop
  have hConn : ContDiffAt ℝ ∞
      (fun q : JBg => backgroundConnectionContraction q.1.1 q.2.1) q₀ := by
    exact ContDiffAt.comp (x := q₀)
      (f := fun q : JBg => (q.1.1, q.2.1))
      (g := fun z : (E3 →L[ℝ] E3) × T3 => backgroundConnectionContraction z.1 z.2)
      (background_connection_contraction_smooth A T c hc hA) hPair
  have hConnCoord : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg => (backgroundConnectionContraction q.1.1 q.2.1) k) q₀ := by
    intro k
    simpa [Function.comp_def, EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp q₀ hConn)
  have hPcoord : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg => (q.1.2 k (EuclideanSpace.single ij.2 1)) ij.1) q₀ := by
    intro k
    fun_prop
  have hAcoord : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg => (q.1.1 (EuclideanSpace.single k 1)) ij.2) q₀ := by
    intro k
    fun_prop
  have hAcoord' : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg => (q.1.1 (EuclideanSpace.single k 1)) ij.1) q₀ := by
    intro k
    fun_prop
  have hJet : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg => backgroundContractionJet q.1.1 q.1.2 q.2.1 q.2.2 ij.1 k) q₀ := by
    intro k
    exact background_jet_smooth A P T R c hc hA ij.1 k
  have hJet' : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg => backgroundContractionJet q.1.1 q.1.2 q.2.1 q.2.2 ij.2 k) q₀ := by
    intro k
    exact background_jet_smooth A P T R c hc hA ij.2 k
  have hFirstTerm : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg =>
        (backgroundConnectionContraction q.1.1 q.2.1) k *
          (q.1.2 k (EuclideanSpace.single ij.2 1)) ij.1) q₀ := by
    intro k
    exact (hConnCoord k).mul (hPcoord k)
  have hFirstSum : ContDiffAt ℝ ∞
      (fun q : JBg => ∑ k : Fin 3,
        (backgroundConnectionContraction q.1.1 q.2.1) k *
          (q.1.2 k (EuclideanSpace.single ij.2 1)) ij.1) q₀ := by
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun k _ => hFirstTerm k))
  have hSecondTerm : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun q : JBg =>
        (q.1.1 (EuclideanSpace.single k 1)) ij.2 *
            backgroundContractionJet q.1.1 q.1.2 q.2.1 q.2.2 ij.1 k +
          (q.1.1 (EuclideanSpace.single k 1)) ij.1 *
            backgroundContractionJet q.1.1 q.1.2 q.2.1 q.2.2 ij.2 k) q₀ := by
    intro k
    exact ((hAcoord k).mul (hJet k)).add
      ((hAcoord' k).mul (hJet' k))
  have hSecondSum : ContDiffAt ℝ ∞
      (fun q : JBg => ∑ k : Fin 3,
        ((q.1.1 (EuclideanSpace.single k 1)) ij.2 *
            backgroundContractionJet q.1.1 q.1.2 q.2.1 q.2.2 ij.1 k +
          (q.1.1 (EuclideanSpace.single k 1)) ij.1 *
            backgroundContractionJet q.1.1 q.1.2 q.2.1 q.2.2 ij.2 k)) q₀ := by
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun k _ => hSecondTerm k))
  have hCorrection : ContDiffAt ℝ ∞
      (fun q : JBg => backgroundLieCorrection q.1.1 q.1.2 q.2.1 q.2.2 ij.1 ij.2) q₀ := by
    simpa [backgroundLieCorrection] using hFirstSum.add hSecondSum
  exact hDetCoord.sub hCorrection
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
