import MorganTianLib.Ch01.ManifoldCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle BigOperators
namespace PoincareConjecture.ParallelImplementation.ScalarSectionalTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
/-- **Math.** Actual scalar curvature is the sum of sectional curvatures in a metric basis. -/
theorem scalarCurvatureAt_eq_sum_sectional
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (p : M) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0) :
    MorganTianLib.scalarCurvatureAt g nabla hLC p =
      ∑ i, ∑ j, MorganTianLib.sectionalCurvatureAt g nabla p (b i) (b j) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have horth : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite]
    exact hb
  let B := MorganTianLib.curvatureFormAt g nabla p
  have hB : Riemannian.IsAlgCurvatureForm B :=
    MorganTianLib.isAlgCurvatureForm_curvatureFormAt g nabla hLC p
  have hterm (i j : ι) :
      B (b i) (b j) (b i) (b j) =
        MorganTianLib.sectionalCurvatureAt g nabla p (b i) (b j) := by
    change B (b i) (b j) (b i) (b j) =
      B (b i) (b j) (b i) (b j) / Riemannian.wedgeSq (b i) (b j)
    by_cases hij : i = j
    · subst j
      have hnum : B (b i) (b i) (b i) (b i) = 0 := by
        have hskew := hB.antisymm₁₂ (b i) (b i) (b i) (b i)
        nlinarith [hskew]
      have hden : Riemannian.wedgeSq (b i) (b i) = 0 := by
        simp [Riemannian.wedgeSq]
      rw [hnum, hden]
      simp
    ·
      have hij' : inner ℝ (b i) (b j) = 0 := by
        simpa [hij] using (b.toOrthonormalBasis horth).inner_eq_ite i j
      have hni : ‖b i‖ = 1 := by
        simpa only [Module.Basis.coe_toOrthonormalBasis] using
          (b.toOrthonormalBasis horth).norm_eq_one i
      have hnj : ‖b j‖ = 1 := by
        simpa only [Module.Basis.coe_toOrthonormalBasis] using
          (b.toOrthonormalBasis horth).norm_eq_one j
      have hden : Riemannian.wedgeSq (b i) (b j) = 1 := by
        simp [Riemannian.wedgeSq, hni, hnj, hij']
      rw [hden]
      simp
  calc
    MorganTianLib.scalarCurvatureAt g nabla hLC p =
        ∑ i, ∑ j, B (b i) (b j) (b i) (b j) := by
      simpa [MorganTianLib.scalarCurvatureAt, MorganTianLib.scalarCurvature, B,
        Module.Basis.coe_toOrthonormalBasis] using
        (Riemannian.scalarCurvature_eq_sum hB (b.toOrthonormalBasis horth))
    _ = ∑ i, ∑ j, MorganTianLib.sectionalCurvatureAt g nabla p (b i) (b j) := by
      simp_rw [hterm]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ScalarSectionalTrace
