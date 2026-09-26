import PoincareConjecture.ParallelImplementation.CoupledAffineSolutionStability
import PoincareConjecture.ParallelImplementation.SameWitnessHeatTranslation
import PoincareConjecture.ParallelImplementation.AffineRationalSolutionTranslation
import PoincareConjecture.ParallelImplementation.EncodedStationaryDifference
import PoincareConjecture.ParallelImplementation.UniformStationaryFullJetDifference
import PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
import PoincareConjecture.ParallelImplementation.FullJetSpatialTranslation
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.UniformAffineRationalDifference
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
open PoincareConjecture.ParallelImplementation.FullJetSpatialTranslation
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance (T : ℝ) : NormedAddCommGroup (FullJet T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (FullJet T) := inferInstance
local instance (T : ℝ) : NormedAddCommGroup (ForcingJet E6 T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (ForcingJet E6 T) := inferInstance
local instance (T : ℝ) (S : Submodule ℝ (FullJet T)) : NormedAddCommGroup S := inferInstance
local instance (T : ℝ) (S : Submodule ℝ (FullJet T)) : NormedSpace ℝ S := inferInstance
local instance (T : ℝ) (S : Submodule ℝ (ForcingJet E6 T)) : NormedAddCommGroup S := inferInstance
local instance (T : ℝ) (S : Submodule ℝ (ForcingJet E6 T)) : NormedSpace ℝ S := inferInstance
open PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient
local notation "A" => E3 →L[ℝ] E3
local notation "V" => E3 →L[ℝ] E6
local notation "H" => E3 →L[ℝ] E3 →L[ℝ] E6
local instance standardGroup0 : NormedAddCommGroup A := inferInstance
local instance standardSpace0 : NormedSpace ℝ A := inferInstance
local instance standardGroup1 : NormedAddCommGroup V := inferInstance
local instance standardSpace1 : NormedSpace ℝ V := inferInstance
local instance standardGroup2 : NormedAddCommGroup H := inferInstance
local instance standardSpace2 : NormedSpace ℝ H := inferInstance
local instance standardGroup3 : NormedAddCommGroup (V →L[ℝ] E6) := inferInstance
local instance standardSpace3 : NormedSpace ℝ (V →L[ℝ] E6) := inferInstance
local instance standardGroup4 : NormedAddCommGroup (A →L[ℝ] V →L[ℝ] V →L[ℝ] E6) := inferInstance
local instance standardSpace4 : NormedSpace ℝ (A →L[ℝ] V →L[ℝ] V →L[ℝ] E6) := inferInstance
local instance standardGroup5 : NormedAddCommGroup (A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] E6) := inferInstance
local instance standardSpace5 : NormedSpace ℝ (A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] E6) := inferInstance

/-- Uniform difference bound for the SAME actual PDE correction and its stationary lift. No evolved uniform estimate is assumed. -/
theorem uniform_affine_rational_difference_bounds
    (T alpha : ℝ) (hT : 0 < T)
    (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T))
    (hX : (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha)
    (hY : (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le)
    (E : E6 →L[ℝ] A) (B : A →L[ℝ] A →L[ℝ] V →L[ℝ] V →L[ℝ] E6)
    (L : Y →L[ℝ] X)
    (P : Y →L[ℝ] ForcingJet A T) (Q : Y →L[ℝ] ForcingJet V T)
    (G : Y →L[ℝ] ForcingJet H T)
    (hPgraph : ∀ y, P y ∈ forcingGraph A T alpha)
    (hQgraph : ∀ y, Q y ∈ forcingGraph V T alpha)
    (hGgraph : ∀ y, G y ∈ forcingGraph H T alpha)
    (hPvalue : ∀ (y : Y) (p : Slab T), (P y).1 p = -E (y.1.1.1.1.1 p))
    (hQvalue : ∀ (y : Y) (p : Slab T), (Q y).1 p = y.1.1.1.1.2.1 p)
    (hGvalue : ∀ (y : Y) (p : Slab T), (G y).1 p = y.1.1.1.1.2.2 p)
    (hLvalue : ∀ (y : Y) (p : Slab T), (L y).1.1 p =
      y.1.1.2 p - ∑ j : Fin 3,
        y.1.1.1.1.2.2 p (EuclideanSpace.single j 1) (EuclideanSpace.single j 1))
    (a : ForcingJet A T) (v : ForcingJet V T) (H0 : ForcingJet H T)
    (f : X) (z : Y) (b : ForcingJet A T)
    (hb : b ∈ forcingGraph A T alpha)
    (heq : ∀ p : Slab T,
      ((1 - (a + P z).1 p) * b.1 p = 1 ∧ b.1 p * (1 - (a + P z).1 p) = 1) ∧
      (L z).1.1 p = f.1.1 p + principalPart (b.1 p - 1) ((H0 + G z).1 p) +
        B (b.1 p) (b.1 p) ((v + Q z).1 p) ((v + Q z).1 p))
    (D : X →L[ℝ] Y) (hLD : L.comp D = ContinuousLinearMap.id ℝ X)
    (R : ℝ) (hR : 0 < R) (hz : ‖z‖ ≤ R)
    (haGraph : a ∈ forcingGraph A T alpha)
    (hvGraph : v ∈ forcingGraph V T alpha)
    (hHGraph : H0 ∈ forcingGraph H T alpha)
    (hsmall : ‖a‖ + ‖P‖ * R ≤ 1 / 2)
    (hcontract : ‖D‖ *
      (18 * (12 * ‖P‖ * (‖H0‖ + ‖G‖ * R) +
        (4 * ‖a‖ + 12 * ‖P‖ * R) * ‖G‖) +
       384 * ‖B‖ * ‖P‖ * (‖v‖ + ‖Q‖ * R) ^ 2 +
       64 * ‖B‖ * ‖Q‖ * (‖v‖ + ‖Q‖ * R)) < 1)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (hE : ‖E‖ ≤ 3)
    (Fu : ForcingJet E6 T) (hFuGraph : Fu ∈ forcingGraph E6 T alpha)
    (hFuValue : ∀ p : Slab T, Fu.1 p = u p.2)
    (haValue : ∀ p : Slab T, a.1 p = -E (Fu.1 p))
    (hvValue : ∀ p : Slab T, v.1 p = fderiv ℝ u p.2)
    (hHValue : ∀ p : Slab T, H0.1 p = fderiv ℝ (fderiv ℝ u) p.2)
    (hfValue : ∀ p : Slab T, f.1.1 p = ∑ j : Fin 3,
      H0.1 p (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin 3) (h : ℝ), h ≠ 0 →
      ‖PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
        z.1 i h‖ ≤ C ∧
      ∀ s : FullJet T,
        (∀ p : Slab T, s.1.1.1.1 p = u p.2 ∧
          s.1.1.1.2.1 p = fderiv ℝ u p.2 ∧
          s.1.1.1.2.2 p = fderiv ℝ (fderiv ℝ u) p.2 ∧ s.1.2 p = 0) →
        (∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T,
          s.1.1.2 p =
            (PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho
              p.1.1 p.1.2 ^ alpha)⁻¹ •
            (s.1.1.1.2.2 p.1.1 - s.1.1.1.2.2 p.1.2)) →
        (∀ p : PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.Pair T,
          s.2 p = 0) →
        ‖PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
          (s + z.1) i h‖ ≤ C :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨Cbg, hCbg, hbg⟩ :=
    PoincareConjecture.ParallelImplementation.EncodedStationaryDifference.uniform_encoded_stationary_differences
      u hu hc E hE alpha halpha halpha1
  obtain ⟨Cstat, hCstat, hstat⟩ :=
    PoincareConjecture.ParallelImplementation.UniformStationaryFullJetDifference.uniform_stationary_full_jet_differences
      u hu hc alpha halpha halpha1
  have hsame :=
    PoincareConjecture.ParallelImplementation.SameWitnessHeatTranslation.same_witness_heat_inverse_translation
      T alpha hT X Y hX hY L D hLD hLvalue
  have hDL : D.comp L = ContinuousLinearMap.id ℝ Y := hsame.2.1
  let S : ℝ := ‖v‖ + ‖Q‖ * R
  let Ky : ℝ :=
    18 * (12 * ‖P‖ * (‖H0‖ + ‖G‖ * R) +
      (4 * ‖a‖ + 12 * ‖P‖ * R) * ‖G‖) +
      384 * ‖B‖ * ‖P‖ * S ^ 2 + 64 * ‖B‖ * ‖Q‖ * S
  let Ka : ℝ := 216 * (‖H0‖ + ‖G‖ * R) + 384 * ‖B‖ * S ^ 2
  let Kv : ℝ := 64 * ‖B‖ * S
  let Kh : ℝ := 18 * (4 * ‖a‖ + 12 * ‖P‖ * R)
  have hcontractKy : ‖D‖ * Ky < 1 := by
    simpa [Ky, S] using hcontract
  have hden : 0 < 1 - ‖D‖ * Ky := by linarith
  have hfac : 0 ≤ ‖D‖ / (1 - ‖D‖ * Ky) := div_nonneg (norm_nonneg _) hden.le
  have hKa : 0 ≤ Ka := by dsimp [Ka, S]; positivity
  have hKv : 0 ≤ Kv := by dsimp [Kv, S]; positivity
  have hKh : 0 ≤ Kh := by dsimp [Kh]; positivity
  let Cq : ℝ := (‖D‖ / (1 - ‖D‖ * Ky)) * (Cbg * (1 + Ka + Kv + Kh))
  have hCq : 0 ≤ Cq := by dsimp [Cq]; positivity
  let C : ℝ := Cstat + Cq
  have hC : 0 < C := by dsimp [C]; linarith [hCstat, hCq]
  refine ⟨C, hC, ?_⟩
  intro i h hh
  have hfGraph : f.1 ∈ forcingGraph E6 T alpha := by
    rw [← hX]
    exact f.2
  have hbgBounds := hbg T hT.le Fu v H0 hFuGraph hvGraph hHGraph
    hFuValue hvValue hHValue a f haGraph hfGraph haValue hfValue i h hh

  let ah : ForcingJet A T := translateForcingJet i h a
  let vh : ForcingJet V T := translateForcingJet i h v
  let Hh : ForcingJet H T := translateForcingJet i h H0
  let bh : ForcingJet A T := translateForcingJet i h b
  have htransA := @forcing_translation_properties A _ _ T alpha i h
  have htransV := @forcing_translation_properties V _ _ T alpha i h
  have htransH := @forcing_translation_properties H _ _ T alpha i h
  have haNorm : ‖ah‖ = ‖a‖ := htransA.2.1 a
  have hvNorm : ‖vh‖ = ‖v‖ := htransV.2.1 v
  have hHNorm : ‖Hh‖ = ‖H0‖ := htransH.2.1 H0
  have haHGraph : ah ∈ forcingGraph A T alpha := (htransA.1 a).2 haGraph
  have hvHGraph : vh ∈ forcingGraph V T alpha := (htransV.1 v).2 hvGraph
  have hHHGraph : Hh ∈ forcingGraph H T alpha := (htransH.1 H0).2 hHGraph

  rcases PoincareConjecture.ParallelImplementation.AffineRationalSolutionTranslation.translate_affine_rational_solution
      T alpha hT X Y hX hY E B L P Q G hPgraph hQgraph hGgraph
      hPvalue hQvalue hGvalue hLvalue a v H0 f z b hb heq i h with
    ⟨zh, fh, hzh, hznorm, hfh, hbhGraph, htranslated⟩

  have hzH : ‖zh‖ ≤ R := by rw [hznorm]; exact hz
  have hsmallH : ‖ah‖ + ‖P‖ * R ≤ 1 / 2 := by
    rw [haNorm]
    exact hsmall
  have hinv0 (p : Slab T) :
      (1 - (a + P z).1 p) * b.1 p = 1 ∧
        b.1 p * (1 - (a + P z).1 p) = 1 := (heq p).1
  have hpde0 (p : Slab T) :
      (L z).1.1 p = f.1.1 p + principalPart (b.1 p - 1) ((H0 + G z).1 p) +
        B (b.1 p) (b.1 p) ((v + Q z).1 p) ((v + Q z).1 p) := (heq p).2
  have hinv1 (p : Slab T) :
      (1 - (ah + P zh).1 p) * bh.1 p = 1 ∧
        bh.1 p * (1 - (ah + P zh).1 p) = 1 := by
    simpa [ah, bh] using (htranslated p).1
  have hpde1 (p : Slab T) :
      (L zh).1.1 p = fh.1.1 p + principalPart (bh.1 p - 1) ((Hh + G zh).1 p) +
        B (bh.1 p) (bh.1 p) ((vh + Q zh).1 p) ((vh + Q zh).1 p) := by
    simpa [bh, Hh, vh] using (htranslated p).2

  have hstableRaw :=
    PoincareConjecture.ParallelImplementation.CoupledAffineSolutionStability.coupled_affine_solution_stability
      T alpha R hR X hX B a ah haGraph haHGraph v vh hvGraph hvHGraph
      H0 Hh hHGraph hHHGraph P Q G hPgraph hQgraph hGgraph hsmall hsmallH
      L D hDL z zh hz hzH f fh b bh hinv0 hinv1 hpde0 hpde1
  have hcontractH : ‖D‖ *
      (18 * (12 * ‖P‖ * (max ‖H0‖ ‖Hh‖ + ‖G‖ * R) +
        (4 * max ‖a‖ ‖ah‖ + 12 * ‖P‖ * R) * ‖G‖) +
       384 * ‖B‖ * ‖P‖ * (max ‖v‖ ‖vh‖ + ‖Q‖ * R) ^ 2 +
       64 * ‖B‖ * ‖Q‖ * (max ‖v‖ ‖vh‖ + ‖Q‖ * R)) < 1 := by
    simpa [haNorm, hvNorm, hHNorm] using hcontract
  have hstable : ‖zh - z‖ ≤
      (‖D‖ / (1 - ‖D‖ * Ky)) *
        (‖fh - f‖ + Ka * ‖ah - a‖ + Kv * ‖vh - v‖ + Kh * ‖Hh - H0‖) := by
    simpa [Ky, Ka, Kv, Kh, S, haNorm, hvNorm, hHNorm] using hstableRaw hcontractH

  have hquotA : ‖h⁻¹ • (ah - a)‖ ≤ Cbg := by
    simpa [ah] using hbgBounds.1
  have hquotV : ‖h⁻¹ • (vh - v)‖ ≤ Cbg := by
    simpa [vh] using hbgBounds.2.1
  have hquotH : ‖h⁻¹ • (Hh - H0)‖ ≤ Cbg := by
    simpa [Hh] using hbgBounds.2.2.1
  have hquotF : ‖h⁻¹ • (fh - f)‖ ≤ Cbg := by
    calc
      ‖h⁻¹ • (fh - f)‖ = ‖(h⁻¹ • (fh - f)).1‖ := rfl
      _ = ‖h⁻¹ • (fh.1 - f.1)‖ := by simp
      _ = ‖h⁻¹ • (translateForcingJet i h f.1 - f.1)‖ := by rw [hfh]
      _ ≤ Cbg := hbgBounds.2.2.2
  have hscaleF : |h⁻¹| * ‖fh - f‖ ≤ Cbg := by
    simpa [norm_smul, Real.norm_eq_abs] using hquotF
  have hscaleA : |h⁻¹| * ‖ah - a‖ ≤ Cbg := by
    simpa [norm_smul, Real.norm_eq_abs] using hquotA
  have hscaleV : |h⁻¹| * ‖vh - v‖ ≤ Cbg := by
    simpa [norm_smul, Real.norm_eq_abs] using hquotV
  have hscaleH : |h⁻¹| * ‖Hh - H0‖ ≤ Cbg := by
    simpa [norm_smul, Real.norm_eq_abs] using hquotH
  have hweighted : |h⁻¹| *
      (‖fh - f‖ + Ka * ‖ah - a‖ + Kv * ‖vh - v‖ + Kh * ‖Hh - H0‖) ≤
      Cbg * (1 + Ka + Kv + Kh) := by
    calc
      _ = |h⁻¹| * ‖fh - f‖ + Ka * (|h⁻¹| * ‖ah - a‖) +
          Kv * (|h⁻¹| * ‖vh - v‖) + Kh * (|h⁻¹| * ‖Hh - H0‖) := by ring
      _ ≤ Cbg + Ka * Cbg + Kv * Cbg + Kh * Cbg := by
        nlinarith [hscaleF,
          mul_le_mul_of_nonneg_left hscaleA hKa,
          mul_le_mul_of_nonneg_left hscaleV hKv,
          mul_le_mul_of_nonneg_left hscaleH hKh]
      _ = Cbg * (1 + Ka + Kv + Kh) := by ring
  have hFDzJet :
      PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
        z.1 i h = h⁻¹ • (zh.1 - z.1) := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · ext p
            simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
              PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
              PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
              translateFullJet, hzh]
          · apply Prod.ext
            · ext p
              simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
                PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
                PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
                translateFullJet, hzh]
            · ext p
              simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
                PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
                PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
                translateFullJet, hzh]
        · ext p
          simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
            PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
            PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
            translateFullJet, hzh]
      · ext p
        simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
          PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
          PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
          translateFullJet, hzh]
    · ext p
      simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
        PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
        PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
        translateFullJet, hzh]
  have hFDnorm :
      ‖PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
          z.1 i h‖ = ‖h⁻¹ • (zh - z)‖ := by
    have hval : (h⁻¹ • (zh - z) : Y).1 = h⁻¹ • (zh.1 - z.1) := by simp
    calc
      _ = ‖h⁻¹ • (zh.1 - z.1)‖ := by rw [hFDzJet]
      _ = ‖(h⁻¹ • (zh - z : Y)).1‖ := by rw [← hval]
      _ = ‖h⁻¹ • (zh - z : Y)‖ := rfl
  have hFDz :
      ‖PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
          z.1 i h‖ ≤ Cq := by
    rw [hFDnorm]
    dsimp [Cq]
    calc
      ‖h⁻¹ • (zh - z)‖ = |h⁻¹| * ‖zh - z‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |h⁻¹| * ((‖D‖ / (1 - ‖D‖ * Ky)) *
          (‖fh - f‖ + Ka * ‖ah - a‖ + Kv * ‖vh - v‖ + Kh * ‖Hh - H0‖)) :=
        mul_le_mul_of_nonneg_left hstable (abs_nonneg _)
      _ = (‖D‖ / (1 - ‖D‖ * Ky)) *
          (|h⁻¹| * (‖fh - f‖ + Ka * ‖ah - a‖ + Kv * ‖vh - v‖ + Kh * ‖Hh - H0‖)) := by ring
      _ ≤ (‖D‖ / (1 - ‖D‖ * Ky)) * (Cbg * (1 + Ka + Kv + Kh)) :=
        mul_le_mul_of_nonneg_left hweighted hfac

  constructor
  · exact hFDz.trans (by
      dsimp [C]
      calc
        Cq = 0 + Cq := by ring
        _ ≤ Cstat + Cq := by linarith [hCstat])
  · intro s hsData hsHessianInc hsTimeInc
    have hFDs := hstat T hT.le s hsData hsHessianInc hsTimeInc i h hh
    have hlinear :
        PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
            (s + z.1) i h =
          PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
              s i h +
            PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
              z.1 i h := by
      apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Prod.ext
            · ext p
              simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
                PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
                PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
                sub_eq_add_neg, smul_add]
              abel
            · apply Prod.ext
              · ext p x
                simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
                  PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
                  PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
                  sub_eq_add_neg, smul_add]
                abel
              · ext p x y
                simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
                  PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
                  PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
                  sub_eq_add_neg, smul_add]
                module
          · ext p
            simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
              PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
              PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
              sub_eq_add_neg, smul_add]
            abel
        · ext p
          simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
            PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
            PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
            sub_eq_add_neg, smul_add]
          abel
      · ext p
        simp [PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet,
          PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.spatialDifferenceBCF,
          PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.pullbackBCF,
          sub_eq_add_neg, smul_add]
        abel
    calc
      ‖PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
          (s + z.1) i h‖ =
          ‖PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
              s i h +
            PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
              z.1 i h‖ := by rw [hlinear]
      _ ≤ ‖PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
            s i h‖ +
          ‖PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet.finiteSpatialDifferenceJet
            z.1 i h‖ := norm_add_le _ _
      _ ≤ Cstat + Cq := add_le_add hFDs hFDz
      _ = C := by rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.UniformAffineRationalDifference
