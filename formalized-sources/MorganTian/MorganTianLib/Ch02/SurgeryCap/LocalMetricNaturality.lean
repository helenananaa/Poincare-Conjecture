import MorganTianLib.Ch01.LeviCivita
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorField.LieBracket
open Set Riemannian
open scoped ContDiff Manifold Topology
noncomputable section
namespace MorganTianLib.SurgeryCap
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [SigmaCompactSpace M] [T2Space M] [SigmaCompactSpace N] [T2Space N]
/-- **Math.** A local metric-preserving diffeomorphism intertwines the actual canonical connections. -/
theorem local_metric_map_covariant_related (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (hmetric : ∀ p u v, g.metricInner p u v = h.metricInner (f p)
      (mfderiv I J f p u) (mfderiv I J f p v))
    (X Y : SmoothVectorField I M) (X' Y' : SmoothVectorField J N)
    (hX : ∀ p, mfderiv I J f p (X p) = X' (f p))
    (hY : ∀ p, mfderiv I J f p (Y p) = Y' (f p)) (p : M) :
    mfderiv I J f p ((leviCivitaConnectionGeneral g).cov X Y p) =
      (leviCivitaConnectionGeneral h).cov X' Y' (f p) := by
/- SWARM_PROOF_BEGIN -/
  letI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact IsManifold.of_le (WithTop.coe_le_coe.2 le_top)
  letI : IsManifold J (minSmoothness ℝ 2) N := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact IsManifold.of_le (WithTop.coe_le_coe.2 le_top)
  have hf_inv : ∀ q : M, (mfderiv I J f q).IsInvertible := by
    intro q
    rw [← (hf q).mfderivToContinuousLinearEquiv_coe (by simp)]
    exact ContinuousLinearMap.isInvertible_equiv
  have hf_diff : ∀ q : M, MDiffAt f q := by
    intro q
    exact (hf q).mdifferentiableAt (by simp)
  have hdir_comp :
      ∀ (A : SmoothVectorField I M) (A' : SmoothVectorField J N),
        (∀ q, mfderiv I J f q (A q) = A' (f q)) →
        ∀ (φ : N → ℝ), MDiffAt φ (f p) →
          A.dir (fun q => φ (f q)) p = A'.dir φ (f p) := by
    intro A A' hA φ hφ
    simp only [SmoothVectorField.dir]
    have hcomp := congrArg (fun L => L (A p))
      (mfderiv_comp p hφ (hf_diff p))
    simpa [Function.comp_def, hA p] using hcomp
  have hbr_comp :
      ∀ (A : SmoothVectorField I M) (A' : SmoothVectorField J N)
        (B : SmoothVectorField I M) (B' : SmoothVectorField J N),
        (∀ q, mfderiv I J f q (A q) = A' (f q)) →
        (∀ q, mfderiv I J f q (B q) = B' (f q)) →
        mfderiv I J f p (DCLieBracket A B p) =
          DCLieBracket A' B' (f p) := by
    intro A A' B B' hA hB
    change mfderiv I J f p
        (VectorField.mlieBracket I A.toFun B.toFun p) =
      VectorField.mlieBracket J A'.toFun B'.toFun (f p)
    have hA' : MDiffAt (T% A'.toFun) (f p) := by
      exact A'.smooth.mdifferentiableAt (by simp)
    have hB' : MDiffAt (T% B'.toFun) (f p) := by
      exact B'.smooth.mdifferentiableAt (by simp)
    have hA_pull :
        VectorField.mpullback I J f A'.toFun = A.toFun := by
      funext q
      change (mfderiv I J f q).inverse (A'.toFun (f q)) = A.toFun q
      exact (hf_inv q).inverse_apply_eq.mpr (hA q).symm
    have hB_pull :
        VectorField.mpullback I J f B'.toFun = B.toFun := by
      funext q
      change (mfderiv I J f q).inverse (B'.toFun (f q)) = B.toFun q
      exact (hf_inv q).inverse_apply_eq.mpr (hB q).symm
    have hnat := VectorField.mpullback_mlieBracket
      hA' hB' (hf p).contMDiffAt (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 le_top)
    change (mfderiv I J f p).inverse
        (VectorField.mlieBracket J A'.toFun B'.toFun (f p)) =
      VectorField.mlieBracket I
        (VectorField.mpullback I J f A'.toFun)
        (VectorField.mpullback I J f B'.toFun) p at hnat
    rw [hA_pull, hB_pull] at hnat
    rw [← hnat]
    exact (hf_inv p).self_apply_inverse _
  apply (h.metricInner_eq_iff_eq (f p) _ _).mp
  intro W
  obtain ⟨Z', hZ'⟩ := exists_smoothVectorField_eq (f p) W
  rw [← hZ']
  let Z : SmoothVectorField I M :=
    { toFun := fun q => VectorField.mpullback I J f Z'.toFun q
      smooth := by
        simpa using
          (ContMDiff.mpullback_vectorField (V := Z'.toFun) (m := ∞) (n := ∞)
            Z'.smooth hf.contMDiff hf_inv (by simp)) }
  have hZ : ∀ q, mfderiv I J f q (Z q) = Z'.toFun (f q) := by
    intro q
    change mfderiv I J f q
        ((mfderiv I J f q).inverse (Z'.toFun (f q))) = _
    exact (hf_inv q).self_apply_inverse _
  have hfun_XZ :
      (fun q => g.metricInner q (X q) (Z q)) =
        (fun q => h.metricInner (f q) (X' (f q)) (Z' (f q))) := by
    funext q
    rw [hmetric q, hX q, hZ q]
  have hfun_ZY :
      (fun q => g.metricInner q (Z q) (Y q)) =
        (fun q => h.metricInner (f q) (Z' (f q)) (Y' (f q))) := by
    funext q
    rw [hmetric q, hZ q, hY q]
  have hfun_YX :
      (fun q => g.metricInner q (Y q) (X q)) =
        (fun q => h.metricInner (f q) (Y' (f q)) (X' (f q))) := by
    funext q
    rw [hmetric q, hY q, hX q]
  have hdir_XZ :
      Y.dir (fun q => g.metricInner q (X q) (Z q)) p =
        Y'.dir (fun q => h.metricInner q (X' q) (Z' q)) (f p) := by
    calc
      Y.dir (fun q => g.metricInner q (X q) (Z q)) p =
          Y.dir (fun q => h.metricInner (f q) (X' (f q)) (Z' (f q))) p := by
            rw [hfun_XZ]
      _ = Y'.dir (fun q => h.metricInner q (X' q) (Z' q)) (f p) :=
        hdir_comp Y Y' hY (fun q => h.metricInner q (X' q) (Z' q))
          (h.metricInner_field_mdifferentiableAt X' Z' (f p))
  have hdir_ZY :
      X.dir (fun q => g.metricInner q (Z q) (Y q)) p =
        X'.dir (fun q => h.metricInner q (Z' q) (Y' q)) (f p) := by
    calc
      X.dir (fun q => g.metricInner q (Z q) (Y q)) p =
          X.dir (fun q => h.metricInner (f q) (Z' (f q)) (Y' (f q))) p := by
            rw [hfun_ZY]
      _ = X'.dir (fun q => h.metricInner q (Z' q) (Y' q)) (f p) :=
        hdir_comp X X' hX (fun q => h.metricInner q (Z' q) (Y' q))
          (h.metricInner_field_mdifferentiableAt Z' Y' (f p))
  have hdir_YX :
      Z.dir (fun q => g.metricInner q (Y q) (X q)) p =
        Z'.dir (fun q => h.metricInner q (Y' q) (X' q)) (f p) := by
    calc
      Z.dir (fun q => g.metricInner q (Y q) (X q)) p =
          Z.dir (fun q => h.metricInner (f q) (Y' (f q)) (X' (f q))) p := by
            rw [hfun_YX]
      _ = Z'.dir (fun q => h.metricInner q (Y' q) (X' q)) (f p) :=
        hdir_comp Z Z' hZ (fun q => h.metricInner q (Y' q) (X' q))
          (h.metricInner_field_mdifferentiableAt Y' X' (f p))
  have hbr_YZ := hbr_comp Y Y' Z Z' hY hZ
  have hbr_XZ := hbr_comp X X' Z Z' hX hZ
  have hbr_YX := hbr_comp Y Y' X X' hY hX
  have hpair_YZ :
      g.metricInner p (DCLieBracket Y Z p) (X p) =
        h.metricInner (f p) (DCLieBracket Y' Z' (f p)) (X' (f p)) := by
    rw [hmetric p, hbr_YZ, hX p]
  have hpair_XZ :
      g.metricInner p (DCLieBracket X Z p) (Y p) =
        h.metricInner (f p) (DCLieBracket X' Z' (f p)) (Y' (f p)) := by
    rw [hmetric p, hbr_XZ, hY p]
  have hpair_YX :
      g.metricInner p (DCLieBracket Y X p) (Z p) =
        h.metricInner (f p) (DCLieBracket Y' X' (f p)) (Z' (f p)) := by
    rw [hmetric p, hbr_YX, hZ p]
  have hRHS : g.koszulRHS Y X Z p = h.koszulRHS Y' X' Z' (f p) := by
    unfold RiemannianMetric.koszulRHS
    rw [hdir_XZ, hdir_ZY, hdir_YX, hpair_YZ, hpair_XZ, hpair_YX]
  have hdual_g := g.koszulDualSection_dual Y X Z p
  have hdual_h := h.koszulDualSection_dual Y' X' Z' (f p)
  have hpair :
      g.metricInner p ((leviCivitaConnectionGeneral g).cov X Y p) (Z p) =
        h.metricInner (f p) ((leviCivitaConnectionGeneral h).cov X' Y' (f p))
          (Z' (f p)) := by
    change g.metricInner p (g.koszulDualSection Y X p) (Z p) =
      h.metricInner (f p) (h.koszulDualSection Y' X' (f p)) (Z' (f p))
    linarith [hdual_g, hdual_h, hRHS]
  calc
    h.metricInner (f p)
        (mfderiv I J f p ((leviCivitaConnectionGeneral g).cov X Y p))
        (Z' (f p)) =
        g.metricInner p ((leviCivitaConnectionGeneral g).cov X Y p) (Z p) := by
          rw [← hZ p]
          exact (hmetric p _ _).symm
    _ = h.metricInner (f p)
        ((leviCivitaConnectionGeneral h).cov X' Y' (f p)) (Z' (f p)) := hpair
/- SWARM_PROOF_END -/
end MorganTianLib.SurgeryCap
