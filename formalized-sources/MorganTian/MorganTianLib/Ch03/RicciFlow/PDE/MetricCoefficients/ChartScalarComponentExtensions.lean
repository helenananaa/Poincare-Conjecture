import MorganTianLib.Ch01.CurvatureFrameBridge
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** chart scalar component extensions. -/
theorem chart_scalar_component_extensions {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (B : E3 ≃L[ℝ] E3)
    (hB : ∀ r : Fin 3, B (EuclideanSpace.single r 1) = Module.finBasis ℝ E3 (e r))
    (x : E3) (hx : B x ∈ (extChartAt (𝓡 3) a).target) (W : E3 → E3) (U : Set E3) (hU : IsOpen U) (hxU : x ∈ U)
    (hW : ContDiffOn ℝ ∞ W U) :
    ∃ f : Fin 3 → M → ℝ, (∀ k, ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (f k)) ∧
      ∀ᶠ q : M in 𝓝 ((extChartAt (𝓡 3) a).symm (B x)), ∀ k : Fin 3,
        f k q = W (B.symm (extChartAt (𝓡 3) a q)) k :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let φ := extChartAt (𝓡 3) a
  let p : M := φ.symm (B x)
  let V : Set M := φ.source ∩ φ ⁻¹' (B.symm ⁻¹' U)
  have hBU : IsOpen (B.symm ⁻¹' U) := hU.preimage B.symm.continuous
  have hV : IsOpen V := by
    exact (continuousOn_extChartAt (I := 𝓡 3) a).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := 𝓡 3) a) hBU
  have hp : p ∈ V := by
    constructor
    · exact φ.map_target hx
    · change B.symm (φ p) ∈ U
      rw [φ.right_inv hx]
      simpa using hxU
  have hchart : ContMDiffOn (𝓡 3) 𝓘(ℝ, E3) ∞ φ φ.source := by
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt (I := 𝓡 3) (x := a)
  have hcoords : ContMDiffOn (𝓡 3) 𝓘(ℝ, E3) ∞
      (fun q : M => B.symm (φ q)) φ.source := by
    exact B.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hchart
  have hW' : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ W U :=
    contMDiffOn_iff_contDiffOn.mpr hW
  have hWcoords : ContMDiffOn (𝓡 3) 𝓘(ℝ, E3) ∞
      (fun q : M => W (B.symm (φ q))) V := by
    have hVeq : V = φ.source ∩ (fun q : M => B.symm (φ q)) ⁻¹' U := by
      ext q
      rfl
    rw [hVeq]
    exact hW'.comp' hcoords
  have hproj (k : Fin 3) : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ) ∞
      (fun z : E3 => z k) := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) k).contMDiff
  have hlocal (k : Fin 3) : ContMDiffOn (𝓡 3) 𝓘(ℝ) ∞
      (fun q : M => W (B.symm (φ q)) k) V := by
    change ContMDiffOn (𝓡 3) 𝓘(ℝ) ∞
      ((fun z : E3 => z k) ∘ (fun q : M => W (B.symm (φ q)))) V
    exact (hproj k).comp_contMDiffOn hWcoords
  have hext (k : Fin 3) : ∃ F : M → ℝ,
      ContMDiff (𝓡 3) 𝓘(ℝ) ∞ F ∧
      ∀ᶠ q : M in 𝓝 p, F q = W (B.symm (φ q)) k :=
    exists_contMDiff_eventuallyEq hV (hlocal k) hp
  let f : Fin 3 → M → ℝ := fun k => Classical.choose (hext k)
  have hf (k : Fin 3) : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (f k) :=
    (Classical.choose_spec (hext k)).1
  have heq (k : Fin 3) : ∀ᶠ q : M in 𝓝 p,
      f k q = W (B.symm (φ q)) k :=
    (Classical.choose_spec (hext k)).2
  refine ⟨f, hf, ?_⟩
  simpa [φ, p] using (Filter.eventually_all.2 heq)
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
