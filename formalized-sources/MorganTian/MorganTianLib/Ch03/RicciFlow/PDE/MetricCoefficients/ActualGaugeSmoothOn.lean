import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** actual gauge contDiffOn. -/
theorem actual_gauge_contDiffOn (G : E3 → (E3 →L[ℝ] E3)) (s : Set E3) (hs : IsOpen s)
    (hG : ContDiffOn ℝ ∞ G s)
    (hpos : ∀ x ∈ s, ∃ c : ℝ, 0 < c ∧ ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) :
    ContDiffOn ℝ ∞ (fun y : E3 => (WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k) : E3)) s :=
/- SWARM_PROOF_BEGIN -/
by
  let firstJet : E3 → Fin 3 → E3 →L[ℝ] E3 := fun y a =>
    fderiv ℝ G y (EuclideanSpace.single a 1)
  let gauge : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) → E3 := fun z =>
    (WithLp.toLp 2 (fun k : Fin 3 => coordinateDeTurckGauge z.1 z.2 k) : E3)
  have hFderiv : ContDiffOn ℝ ∞ (fderiv ℝ G) s :=
    hG.fderiv_of_isOpen hs (m := ∞) (by simp)
  have hJet : ContDiffOn ℝ ∞ firstJet s := by
    rw [contDiffOn_pi]
    intro a
    simpa [firstJet] using
      (hFderiv.clm_apply (contDiffOn_const :
        ContDiffOn ℝ ∞ (fun _ : E3 => (EuclideanSpace.single a (1 : ℝ) : E3)) s))
  have hInput : ContDiffOn ℝ ∞ (fun y : E3 => (G y, firstJet y)) s :=
    hG.prodMk hJet
  apply hs.contDiffOn_iff.mpr
  intro y hy
  have hLocal := coordinate_deturck_gauge_smooth (G y) (firstJet y) (Classical.choose (hpos y hy))
    (Classical.choose_spec (hpos y hy)).1 (Classical.choose_spec (hpos y hy)).2
  have hInputAt : ContDiffAt ℝ ∞ (fun y : E3 => (G y, firstJet y)) y :=
    hInput.contDiffAt (hs.mem_nhds hy)
  have hComp : ContDiffAt ℝ ∞ (gauge ∘ (fun y : E3 => (G y, firstJet y))) y :=
    hLocal.comp y hInputAt
  simpa [gauge, firstJet, Function.comp_def] using hComp
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
