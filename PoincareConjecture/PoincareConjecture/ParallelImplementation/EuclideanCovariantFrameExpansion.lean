import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanCovariantFrameExpansion
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem covariant_derivative_in_frame
    (D : Riemannian.AffineConnection 𝓘(ℝ, E3) E3)
    (V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3)
    (hV : ∀ (i : Idx) (x : E3), V i x = EuclideanSpace.single i 1)
    (G : E3 → First)
    (hG : ∀ (x : E3) (i j k : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) ((D.cov (V i) (V j)) x) = G x k i j) :

    ∀ (W : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3) (x : E3) (i k : Idx),
      (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) ((D.cov (V i) W) x) = fderiv ℝ (fun y : E3 => (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) (W y)) x (EuclideanSpace.single i 1) +
        ∑ j : Idx, G x k i j * (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) j : E3 →L[ℝ] ℝ) (W x) :=
/- SWARM_PROOF_BEGIN -/
by
  intro W x i k
  classical
  letI : AddCommMonoid (Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3) := {
    add_assoc a b c := Riemannian.SmoothVectorField.ext fun y => add_assoc (a y) (b y) (c y)
    zero_add a := Riemannian.SmoothVectorField.ext fun y => zero_add (a y)
    add_zero a := Riemannian.SmoothVectorField.ext fun y => add_zero (a y)
    add_comm a b := Riemannian.SmoothVectorField.ext fun y => add_comm (a y) (b y)
    nsmul := nsmulRec }
  let π : Idx → E3 →L[ℝ] ℝ := fun j =>
    PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) j
  let f : Idx → E3 → ℝ := fun j y => π j (W y)
  have hWcont : ContDiff ℝ ∞ (W : E3 → E3) :=
    contMDiff_vectorSpace_iff_contDiff.mp W.smooth
  have hf : ∀ j : Idx, ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (f j) := by
    intro j
    have hc : ContDiff ℝ ∞ (f j) := (π j).contDiff.comp hWcont
    exact hc.contMDiff
  have hrepr (z : E3) : ∑ j : Idx, π j z • EuclideanSpace.single j 1 = z := by
    simpa [π, PiLp.proj_apply] using (EuclideanSpace.basisFun Idx ℝ).sum_repr z
  have hsumApply (s : Finset Idx) (U : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3)
      (y : E3) : (∑ j ∈ s, U j) y = ∑ j ∈ s, U j y := by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, Riemannian.SmoothVectorField.add_apply, ih]
  have hdecomp : W = ∑ j : Idx, Riemannian.SmoothVectorField.smul (f j) (hf j) (V j) := by
    ext y
    rw [hsumApply]
    simp only [Riemannian.SmoothVectorField.smul_apply]
    rw [← hrepr (W y)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hV j y]
  have hdir (j : Idx) :
      (V i).dir (f j) x = fderiv ℝ (fun y : E3 => π j (W y)) x
          (EuclideanSpace.single i 1) := by
    change mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (f j) x (V i x) = _
    rw [mfderiv_eq_fderiv, hV i x]
    rfl
  have hcovSum (s : Finset Idx) :
      (D.cov (V i) (∑ j ∈ s, Riemannian.SmoothVectorField.smul (f j) (hf j) (V j))) x =
        ∑ j ∈ s, ((V i).dir (f j) x • V j x +
          f j x • (D.cov (V i) (V j)) x) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using D.cov_zero_right (V i) x
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, D.add_right]
        simp only [Riemannian.SmoothVectorField.add_apply]
        rw [D.leibniz (f a) (hf a) (V i) (V a) x, ih, Finset.sum_insert ha]
        abel
  have hcov :
      (D.cov (V i) W) x =
        ∑ j : Idx, ((V i).dir (f j) x • V j x +
          f j x • (D.cov (V i) (V j)) x) := by
    rw [hdecomp]
    simpa using hcovSum Finset.univ
  have hproj : π k ((D.cov (V i) W) x) =
      ∑ j : Idx, ((V i).dir (f j) x * π k (V j x) +
        f j x * π k ((D.cov (V i) (V j)) x)) := by
    rw [hcov]
    simp only [map_sum, map_add, map_smul, smul_eq_mul]
  have hframe (j : Idx) : π k (V j x) = if j = k then 1 else 0 := by
    rw [hV j x]
    simp [π, PiLp.proj_apply, PiLp.single_apply, eq_comm]
  have hderivSum :
      (∑ j : Idx, (V i).dir (f j) x * π k (V j x)) =
        fderiv ℝ (fun y : E3 => π k (W y)) x (EuclideanSpace.single i 1) := by
    rw [Finset.sum_eq_single k]
    · rw [hframe]
      simp only [ite_true, mul_one]
      exact hdir k
    · intro j hj hjne
      rw [hframe]
      simp [hjne]
    · simp
  calc
    π k ((D.cov (V i) W) x) =
        ∑ j : Idx, ((V i).dir (f j) x * π k (V j x) +
          f j x * π k ((D.cov (V i) (V j)) x)) := hproj
    _ = fderiv ℝ (fun y : E3 => π k (W y)) x (EuclideanSpace.single i 1) +
          ∑ j : Idx, G x k i j * π j (W x) := by
      rw [Finset.sum_add_distrib, hderivSum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hG x i j k]
      dsimp [f]
      exact mul_comm _ _
    _ = _ := rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanCovariantFrameExpansion
