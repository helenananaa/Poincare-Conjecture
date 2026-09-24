import PoincareConjecture.ParallelImplementation.ConformalSectionalRecovered
import Mathlib
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle
namespace PoincareConjecture.ParallelImplementation.ConformalSectionalPerturbation
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
/-- A quantitative curvature perturbation estimate uses actual small conformal jets. -/
theorem conformal_sectional_perturbation_bound (g : RiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (X Y : SmoothVectorField I M) (p : M)
    (delta K A B : ℝ) (hd : 0 ≤ delta) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX : g.metricInner p (X p) (X p) = 1) (hY : g.metricInner p (Y p) (Y p) = 1)
    (hXY : g.metricInner p (X p) (Y p) = 0) (hvalue : |u p| ≤ delta)
    (hbase : |MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection p (X p) (Y p)| ≤ K)
    (hHXX : |MorganTianLib.hessian g.leviCivitaConnection u X X p| ≤ A)
    (hHYY : |MorganTianLib.hessian g.leviCivitaConnection u Y Y p| ≤ A)
    (hgrad : g.metricInner p (MorganTianLib.gradientField g u hu p)
      (MorganTianLib.gradientField g u hu p) ≤ B) :
    |MorganTianLib.sectionalCurvatureAt (conformalMetric g u hu)
      (conformalMetric g u hu).leviCivitaConnection p (X p) (Y p) -
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection p (X p) (Y p)| ≤
      (Real.exp (2*delta)-1)*K + Real.exp (2*delta)*(2*A+3*B) :=
/- SWARM_PROOF_BEGIN -/
by
  let G := MorganTianLib.gradientField g u hu
  let k := MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection p (X p) (Y p)
  let q := g.metricInner p (G p) (G p)
  let a := X.dir u p
  let b := Y.dir u p
  let hxx := MorganTianLib.hessian g.leviCivitaConnection u X X p
  let hyy := MorganTianLib.hessian g.leviCivitaConnection u Y Y p
  let c := Real.exp (-2 * u p)
  let D := 2 * delta
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have huD : |(-2 * u p)| ≤ D := by
    dsimp [D]
    calc
      |(-2) * u p| = 2 * |u p| := by rw [abs_mul]; norm_num
      _ ≤ 2 * delta := by nlinarith [hvalue]
  have hargUpper : -2 * u p ≤ D := le_trans (le_abs_self _) huD
  have hcUpper : c ≤ Real.exp D := by
    dsimp [c]
    exact Real.exp_le_exp.mpr hargUpper
  have hargLower : -D ≤ -2 * u p := by
    exact neg_le_of_abs_le huD
  have hcLower : Real.exp (-D) ≤ c := by
    dsimp [c]
    exact Real.exp_le_exp.mpr hargLower
  have hsumExp : 2 ≤ Real.exp D + Real.exp (-D) := by
    have h1 := Real.add_one_le_exp D
    have h2 := Real.add_one_le_exp (-D)
    linarith
  have hdown : 1 - Real.exp (-D) ≤ Real.exp D - 1 := by linarith
  have hdiff : |c - 1| ≤ Real.exp D - 1 := by
    apply (abs_le).2
    constructor <;> linarith [hcLower, hcUpper, hdown]
  have hqNonneg : 0 ≤ q := by dsimp [q, G]; exact g.metricInner_self_nonneg p _
  have hqBound : q ≤ B := by dsimp [q, G]; exact hgrad
  have hdirX : a = g.metricInner p (G p) (X p) := by
    dsimp [a, G]
    exact (MorganTianLib.metricInner_gradientField_eq_dir g hu X p).symm
  have hdirY : b = g.metricInner p (G p) (Y p) := by
    dsimp [b, G]
    exact (MorganTianLib.metricInner_gradientField_eq_dir g hu Y p).symm
  have haBound : a ^ 2 ≤ B := by
    have hproj : 0 ≤ g.metricInner p (G p - a • X p) (G p - a • X p) :=
      g.metricInner_self_nonneg p _
    simp only [g.metricInner_sub_left, g.metricInner_sub_right,
      g.metricInner_smul_left, g.metricInner_smul_right] at hproj
    rw [g.metricInner_comm p (X p) (G p), hdirX.symm, hX] at hproj
    have hsq : a ^ 2 ≤ q := by nlinarith [hproj]
    exact hsq.trans hqBound
  have hbBound : b ^ 2 ≤ B := by
    have hproj : 0 ≤ g.metricInner p (G p - b • Y p) (G p - b • Y p) :=
      g.metricInner_self_nonneg p _
    simp only [g.metricInner_sub_left, g.metricInner_sub_right,
      g.metricInner_smul_left, g.metricInner_smul_right] at hproj
    rw [g.metricInner_comm p (Y p) (G p), hdirY.symm, hY] at hproj
    have hsq : b ^ 2 ≤ q := by nlinarith [hproj]
    exact hsq.trans hqBound
  have hqAbs : |q| ≤ B := by rw [abs_of_nonneg hqNonneg]; exact hqBound
  have herr : |(-hxx - hyy + a ^ 2 + b ^ 2 - q)| ≤ 2 * A + 3 * B := by
    have hhxx : |hxx| ≤ A := by simpa [hxx] using hHXX
    have hhyy : |hyy| ≤ A := by simpa [hyy] using hHYY
    have htri :
        |(-hxx - hyy + a ^ 2 + b ^ 2 - q)| ≤
          |hxx| + |hyy| + |a ^ 2| + |b ^ 2| + |q| := by
      have h1 := abs_add_le ((-hxx - hyy + a ^ 2 + b ^ 2)) (-q)
      have h2 := abs_add_le ((-hxx - hyy + a ^ 2)) (b ^ 2)
      have h3 := abs_add_le (-hxx - hyy) (a ^ 2)
      have h4 := abs_add_le (-hxx) (-hyy)
      simp only [abs_neg, sub_eq_add_neg] at h1 h2 h3 h4 ⊢
      linarith [h1, h2, h3, h4]
    have hsqA : |a ^ 2| ≤ B := by rw [abs_of_nonneg (sq_nonneg a)]; exact haBound
    have hsqB : |b ^ 2| ≤ B := by rw [abs_of_nonneg (sq_nonneg b)]; exact hbBound
    linarith
  have herrNonneg : 0 ≤ 2 * A + 3 * B := by positivity
  let e := -hxx - hyy + a ^ 2 + b ^ 2 - q
  have hnew :=
    PoincareConjecture.ParallelImplementation.ConformalSectionalRecovered.sectionalCurvatureAt_conformalMetric
      g u hu X Y p hX hY hXY
  have hnew' :
      MorganTianLib.sectionalCurvatureAt (conformalMetric g u hu)
        (conformalMetric g u hu).leviCivitaConnection p (X p) (Y p) = c * (k + e) := by
    rw [hnew]
    dsimp [c, k, e, q, G, hxx, hyy, a, b]
    ring
  have halg : c * (k + e) - k = (c - 1) * k + c * e := by ring
  have hcpos : 0 ≤ c := (Real.exp_pos _).le
  have hstep1 : |(c - 1) * k| + |c * e| ≤ |c - 1| * K + c * (2 * A + 3 * B) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hcpos]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hbase (abs_nonneg _))
      (mul_le_mul_of_nonneg_left herr hcpos)
  have hstep2 : |c - 1| * K + c * (2 * A + 3 * B) ≤
      (Real.exp (2 * delta) - 1) * K + Real.exp (2 * delta) * (2 * A + 3 * B) := by
    simpa [D] using add_le_add
      (mul_le_mul_of_nonneg_right hdiff hK)
      (mul_le_mul_of_nonneg_right hcUpper herrNonneg)
  rw [hnew']
  change |c * (k + e) - k| ≤ _
  rw [halg]
  exact (abs_add_le ((c - 1) * k) (c * e)).trans (hstep1.trans hstep2)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalSectionalPerturbation
