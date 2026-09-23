import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedHolderGraphNorm
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedHolderIncrement
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHolderOperator
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ProbabilityConvolutionLinear
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** holder graph heat contraction. -/
theorem holder_graph_heat_contraction 
    (B : E3 ≃L[ℝ] E3) (alpha t : ℝ) (ha : 0 < alpha) (ht : 0 < t) :
    ∃ S : (boundedHolderGraph ℝ alpha) → (boundedHolderGraph ℝ alpha),
      (∀ z, ∀ x : E3, (S z).1.1 x =
        ∫ y : E3, anisotropicHeatKernel B t y*z.1.1 (x-y)) ∧
      ∀ z w, dist (S z) (S w) ≤ dist z w :=
/- SWARM_PROOF_BEGIN -/
by
  rcases anisotropic_heat_kernel_mass B t ht with ⟨hK, hMass, hKpos⟩
  obtain ⟨C, hCnorm, hCformula⟩ :=
    probability_convolution_linear (anisotropicHeatKernel B t) hK hKpos hMass
  have hholder (f : E3 →ᵇ ℝ) (H : ℝ) (hH : 0 ≤ H)
      (hf : ∀ x y : E3, ‖f x - f y‖ ≤ H * ‖x-y‖^alpha) :
      ∀ x y : E3, |(C f) x - (C f) y| ≤ H * ‖x-y‖^alpha := by
    have hp := probability_convolution_holder (anisotropicHeatKernel B t)
      hK hKpos hMass f alpha H hH (by
        intro x y
        simpa [Real.norm_eq_abs] using hf x y)
    intro x y
    simpa only [hCformula f x, hCformula f y] using hp.2.2 x y
  have hinc (z : boundedHolderGraph ℝ alpha) :
      ∃ Q : Ω →ᵇ ℝ, ‖Q‖ ≤ ‖z.1.2‖ ∧
        ∀ p : Ω, Q p = (‖p.1.1-p.1.2‖^alpha)⁻¹ •
          ((C z.1.1) p.1.1 - (C z.1.1) p.1.2) := by
    have hz := bounded_holder_graph_norm alpha z.1 z.2
    apply bounded_holder_increment alpha ‖z.1.2‖ (norm_nonneg _) (C z.1.1)
    intro x y
    have hout := hholder z.1.1 ‖z.1.2‖ (norm_nonneg _) hz.1
    have hxy := hout x y
    simpa [Real.norm_eq_abs] using hxy
  let Q (z : boundedHolderGraph ℝ alpha) : Ω →ᵇ ℝ := Classical.choose (hinc z)
  have hQ (z : boundedHolderGraph ℝ alpha) :
      ‖Q z‖ ≤ ‖z.1.2‖ ∧
        ∀ p : Ω, Q z p = (‖p.1.1-p.1.2‖^alpha)⁻¹ •
          ((C z.1.1) p.1.1 - (C z.1.1) p.1.2) :=
    Classical.choose_spec (hinc z)
  have houtGraph (z : boundedHolderGraph ℝ alpha) :
      ((C z.1.1), Q z) ∈ boundedHolderGraph ℝ alpha := by
    intro p
    exact (hQ z).2 p
  let S : (boundedHolderGraph ℝ alpha) → (boundedHolderGraph ℝ alpha) :=
    fun z => ⟨((C z.1.1), Q z), houtGraph z⟩
  refine ⟨S, ?_, ?_⟩
  · intro z x
    exact hCformula z.1.1 x
  · intro z w
    have hdiffGraph : z.1 - w.1 ∈ boundedHolderGraph ℝ alpha := by
      intro p
      change z.1.2 p - w.1.2 p =
        (‖p.1.1-p.1.2‖^alpha)⁻¹ •
          ((z.1.1 p.1.1 - w.1.1 p.1.1) - (z.1.1 p.1.2 - w.1.1 p.1.2))
      rw [z.2 p, w.2 p]
      rw [← smul_sub]
      congr 1
      ring
    have hdiffNorm := bounded_holder_graph_norm alpha (z.1 - w.1) hdiffGraph
    have hconvDiff := hholder (z.1.1-w.1.1) ‖z.1.2-w.1.2‖
      (norm_nonneg _) (by
        intro x y
        simpa [Real.norm_eq_abs] using hdiffNorm.1 x y)
    have hdiffOutput (x y : E3) :
        ‖C (z.1.1-w.1.1) x - C (z.1.1-w.1.1) y‖ ≤
          ‖z.1.2-w.1.2‖ * ‖x-y‖^alpha := by
      rw [Real.norm_eq_abs]
      simpa only [hCformula (z.1.1-w.1.1) x, hCformula (z.1.1-w.1.1) y] using
        hconvDiff x y
    obtain ⟨R, hRnorm, hRformula⟩ :=
      bounded_holder_increment alpha ‖z.1.2-w.1.2‖ (norm_nonneg _)
        (C (z.1.1-w.1.1)) hdiffOutput
    have hlinear : C (z.1.1-w.1.1) = C z.1.1 - C w.1.1 := map_sub C _ _
    have hlinearEval (x : E3) :
        C (z.1.1-w.1.1) x = C z.1.1 x - C w.1.1 x := by
      rw [hlinear]
      rfl
    have hQdiff : Q z - Q w = R := by
      ext p
      change Q z p - Q w p = R p
      rw [(hQ z).2 p, (hQ w).2 p, hRformula p]
      rw [← smul_sub]
      congr 1
      rw [hlinearEval p.1.1, hlinearEval p.1.2]
      ring
    have hfirst : dist (S z).1.1 (S w).1.1 ≤ dist z.1.1 w.1.1 := by
      rw [dist_eq_norm, dist_eq_norm]
      calc
        ‖C z.1.1 - C w.1.1‖ = ‖C (z.1.1-w.1.1)‖ := by rw [map_sub]
        _ ≤ ‖C‖ * ‖z.1.1-w.1.1‖ := C.le_opNorm _
        _ ≤ 1 * ‖z.1.1-w.1.1‖ :=
          mul_le_mul_of_nonneg_right hCnorm (norm_nonneg _)
        _ = ‖z.1.1-w.1.1‖ := one_mul _
    have hsecond : dist (S z).1.2 (S w).1.2 ≤ dist z.1.2 w.1.2 := by
      rw [dist_eq_norm, dist_eq_norm]
      change ‖Q z - Q w‖ ≤ ‖z.1.2-w.1.2‖
      rw [hQdiff]
      exact hRnorm
    change dist ((S z).1) ((S w).1) ≤ dist z.1 w.1
    rw [Prod.dist_eq, Prod.dist_eq]
    exact max_le (hfirst.trans (le_max_left _ _))
      (hsecond.trans (le_max_right _ _))
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
