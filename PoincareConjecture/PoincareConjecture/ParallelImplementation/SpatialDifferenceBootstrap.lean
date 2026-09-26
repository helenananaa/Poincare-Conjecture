import PoincareConjecture.ParallelImplementation.C2HolderPointwiseLimit
import PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SpatialDifferenceBootstrap
open PoincareConjecture.ParallelImplementation.UniformInitialDifferenceQuotient
open scoped ContDiff Topology
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
def spatialQuotient (w : E3 → E6) (i : Fin 3) (h : ℝ) : E3 → E6 :=
  differenceQuotient w h (EuclideanSpace.single i 1)
/-- The actual spatial difference bounds upgrade a C2 field to C3.
Neither convergence of derivative jets nor C3 regularity is assumed. -/
theorem contDiff_three_of_uniform_spatial_differences
    (w : E3 → E6) (hw : ContDiff ℝ 2 w)
    (C alpha : ℝ) (hC : 0 ≤ C) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hbound : ∀ (i : Fin 3) (h : ℝ), h ≠ 0 → ∀ x : E3,
      ‖spatialQuotient w i h x‖ ≤ C ∧
      ‖fderiv ℝ (spatialQuotient w i h) x‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (spatialQuotient w i h)) x‖ ≤ C)
    (hholder : ∀ (i : Fin 3) (h : ℝ), h ≠ 0 → ∀ x y : E3,
      ‖fderiv ℝ (fderiv ℝ (spatialQuotient w i h)) x -
        fderiv ℝ (fderiv ℝ (spatialQuotient w i h)) y‖ ≤ C * ‖x-y‖ ^ alpha) :
    ContDiff ℝ 3 w :=
/- SWARM_PROOF_BEGIN -/
by
  let hseq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hseqPos (n : ℕ) : 0 < hseq n := by
    dsimp [hseq]
    positivity
  have hseqNe (n : ℕ) : hseq n ≠ 0 := (hseqPos n).ne'
  have hseqLim : Filter.Tendsto hseq Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [hseq, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)))
  have hseqPosLim : Filter.Tendsto hseq Filter.atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hseqLim, Filter.Eventually.of_forall hseqPos⟩
  have hquotC2 (i : Fin 3) (h : ℝ) :
      ContDiff ℝ 2 (spatialQuotient w i h) := by
    change ContDiff ℝ 2
      (fun x : E3 => h⁻¹ • (w (x + h • EuclideanSpace.single i 1) - w x))
    have harg : ContDiff ℝ 2 (fun x : E3 => x + h • EuclideanSpace.single i 1) := by
      exact (contDiff_id.add contDiff_const).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact ((hw.comp harg).sub hw).const_smul (h⁻¹)
  let coord (i : Fin 3) : E3 → E6 := fun x =>
    fderiv ℝ w x (EuclideanSpace.single i 1)
  have hcoord (i : Fin 3) : ContDiff ℝ 2 (coord i) := by
    let u : ℕ → E3 → E6 := fun n => spatialQuotient w i (hseq n)
    have hu : ∀ n, ContDiff ℝ 2 (u n) := by
      intro n
      exact hquotC2 i (hseq n)
    have hlim (x : E3) : Filter.Tendsto (fun n => u n x) Filter.atTop (𝓝 (coord i x)) := by
      have hline : HasLineDerivAt ℝ w (fderiv ℝ w x (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) :=
        (hw.differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt _
      have h := hline.tendsto_slope_zero_right.comp hseqPosLim
      simpa [Function.comp_def, u, coord, spatialQuotient, differenceQuotient] using h
    exact
      (PoincareConjecture.ParallelImplementation.C2HolderPointwiseLimit.contDiff_two_of_uniform_holder_pointwise_limit
        u (coord i) C alpha hC ha ha1 hu
        (fun n x => hbound i (hseq n) (hseqNe n) x)
        (fun n x y => hholder i (hseq n) (hseqNe n) x y)
        hlim).1
  have hcoord_apply (y : E3) :
      ContDiff ℝ 2 (fun x : E3 => fderiv ℝ w x y) := by
    have hy : y = ∑ i : Fin 3, y i • EuclideanSpace.single i 1 := by
      ext j
      simp [Pi.single_apply]
    have hrepr (x : E3) : fderiv ℝ w x y = ∑ i : Fin 3, y i • coord i x := by
      calc
        fderiv ℝ w x y =
            fderiv ℝ w x (∑ i : Fin 3, y i • EuclideanSpace.single i 1) :=
          congrArg (fderiv ℝ w x) hy
        _ = ∑ i : Fin 3, y i • coord i x := by simp [coord]
    rw [show (fun x : E3 => fderiv ℝ w x y) =
      (∑ i : Fin 3, fun x : E3 => y i • coord i x) by
        funext x
        exact hrepr x]
    exact ContDiff.sum (s := Finset.univ)
      (fun i hi => (hcoord i).const_smul (y i))
  have hDf : ContDiff ℝ 2 (fderiv ℝ w) := by
    rw [contDiff_clm_apply_iff]
    exact hcoord_apply
  have hresult : ContDiff ℝ (2 + 1 : ℕ∞ω) w := by
    rw [contDiff_succ_iff_fderiv]
    exact ⟨hw.differentiable (by norm_num), by simp, hDf⟩
  have hlevel : (2 + 1 : ℕ∞ω) = 3 := by norm_num
  rw [← hlevel]
  exact hresult
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SpatialDifferenceBootstrap
