import PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
import PoincareConjecture.ParallelImplementation.FullJetSpatialTranslation
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AffineRationalSolutionTranslation
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
open PoincareConjecture.ParallelImplementation.FullJetSpatialTranslation
open scoped Topology BigOperators BoundedContinuousFunction
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
/-- Translate an actual affine rational PDE solution in the original spaces.
Projection covariance is derived from their component formulas, not assumed. -/
theorem translate_affine_rational_solution
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
    (i : Fin 3) (h : ℝ) :
    ∃ zh : Y, ∃ fh : X,
      zh.1 = translateFullJet i h z.1 ∧ ‖zh‖ = ‖z‖ ∧
      fh.1 = translateForcingJet i h f.1 ∧
      translateForcingJet i h b ∈ forcingGraph A T alpha ∧
      ∀ p : Slab T,
        ((1 - (translateForcingJet i h a + P zh).1 p) *
          (translateForcingJet i h b).1 p = 1 ∧
         (translateForcingJet i h b).1 p *
          (1 - (translateForcingJet i h a + P zh).1 p) = 1) ∧
        (L zh).1.1 p = fh.1.1 p +
          principalPart ((translateForcingJet i h b).1 p - 1)
            ((translateForcingJet i h H0 + G zh).1 p) +
          B ((translateForcingJet i h b).1 p) ((translateForcingJet i h b).1 p)
            ((translateForcingJet i h v + Q zh).1 p)
            ((translateForcingJet i h v + Q zh).1 p) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases full_jet_translation_properties T alpha hT.le i h with
    ⟨hfullGraph, hfullNorm, _hfullInv, _hfullAdd, _hfullSmul, hfullResidual⟩
  rcases @forcing_translation_properties A _ _ T alpha i h with
    ⟨hAgraph, _hAnorm, _hAinv, _hAadd, _hAsmul⟩
  rcases @forcing_translation_properties V _ _ T alpha i h with
    ⟨_hVgraph, _hVnorm, _hVinv, _hVadd, _hVsmul⟩
  rcases @forcing_translation_properties H _ _ T alpha i h with
    ⟨_hHgraph, _hHnorm, _hHinv, _hHadd, _hHsmul⟩
  have hzFull : (z : FullJet T) ∈ fullParabolicJetSet T alpha hT.le := by
    exact hY ▸ z.2
  have hzTranslated : translateFullJet i h (z : FullJet T) ∈
      fullParabolicJetSet T alpha hT.le := (hfullGraph z).2 hzFull
  have hzTranslatedY : translateFullJet i h (z : FullJet T) ∈ (Y : Set (FullJet T)) := by
    rw [hY]
    exact hzTranslated
  let zh : Y := ⟨translateFullJet i h (z : FullJet T), hzTranslatedY⟩
  have hfGraph : (f : ForcingJet E6 T) ∈ forcingGraph E6 T alpha := by
    have hfmem : (f : ForcingJet E6 T) ∈ (X : Set (ForcingJet E6 T)) := f.2
    exact hX ▸ hfmem
  have hfTranslated : translateForcingJet i h (f : ForcingJet E6 T) ∈
      forcingGraph E6 T alpha :=
    (@forcing_translation_properties E6 _ _ T alpha i h).1 _ |>.2 hfGraph
  have hfTranslatedX : translateForcingJet i h (f : ForcingJet E6 T) ∈
      (X : Set (ForcingJet E6 T)) := by
    rw [hX]
    exact hfTranslated
  let fh : X := ⟨translateForcingJet i h (f : ForcingJet E6 T), hfTranslatedX⟩
  have hzh : (zh : FullJet T) = translateFullJet i h (z : FullJet T) := rfl
  have hfh : (fh : ForcingJet E6 T) = translateForcingJet i h (f : ForcingJet E6 T) := rfl
  have hznorm : ‖zh‖ = ‖z‖ := by
    change ‖translateFullJet i h (z : FullJet T)‖ = ‖(z : FullJet T)‖
    exact hfullNorm z
  have hPcov (p : Slab T) : (P zh).1 p =
      (translateForcingJet i h (P z)).1 p := by
    let q := shiftPoint p i h
    rw [hPvalue zh p, hzh]
    change -E ((translateFullJet i h (z : FullJet T)).1.1.1.1 p) =
      (P z).1 q
    rw [hPvalue z q]
    rfl
  have hQcov (p : Slab T) : (Q zh).1 p =
      (translateForcingJet i h (Q z)).1 p := by
    let q := shiftPoint p i h
    rw [hQvalue zh p, hzh]
    change (translateFullJet i h (z : FullJet T)).1.1.1.2.1 p =
      (Q z).1 q
    rw [hQvalue z q]
    rfl
  have hGcov (p : Slab T) : (G zh).1 p =
      (translateForcingJet i h (G z)).1 p := by
    let q := shiftPoint p i h
    rw [hGvalue zh p, hzh]
    change (translateFullJet i h (z : FullJet T)).1.1.1.2.2 p =
      (G z).1 q
    rw [hGvalue z q]
    rfl
  have hPjet : P zh = translateForcingJet i h (P z) :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (P zh) (translateForcingJet i h (P z))
      (hPgraph zh)
      ((@forcing_translation_properties A _ _ T alpha i h).1 (P z) |>.2
        (hPgraph z)) hPcov
  have hQjet : Q zh = translateForcingJet i h (Q z) :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (Q zh) (translateForcingJet i h (Q z))
      (hQgraph zh)
      ((@forcing_translation_properties V _ _ T alpha i h).1 (Q z) |>.2
        (hQgraph z)) hQcov
  have hGjet : G zh = translateForcingJet i h (G z) :=
    PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha (G zh) (translateForcingJet i h (G z))
      (hGgraph zh)
      ((@forcing_translation_properties H _ _ T alpha i h).1 (G z) |>.2
        (hGgraph z)) hGcov
  have hbTranslated : translateForcingJet i h b ∈ forcingGraph A T alpha :=
    (hAgraph b).2 hb
  refine ⟨zh, fh, hzh, hznorm, hfh, hbTranslated, ?_⟩
  intro p
  let q := shiftPoint p i h
  have hPfactor : (translateForcingJet i h a + P zh).1 p = (a + P z).1 q := by
    change (translateForcingJet i h a).1 p + (P zh).1 p = a.1 q + (P z).1 q
    rw [hPcov]
    rfl
  have hbval : (translateForcingJet i h b).1 p = b.1 q := rfl
  have hHcov : (translateForcingJet i h H0 + G zh).1 p = (H0 + G z).1 q := by
    change (translateForcingJet i h H0).1 p + (G zh).1 p = H0.1 q + (G z).1 q
    rw [hGcov]
    rfl
  have hvcov : (translateForcingJet i h v + Q zh).1 p = (v + Q z).1 q := by
    change (translateForcingJet i h v).1 p + (Q zh).1 p = v.1 q + (Q z).1 q
    rw [hQcov]
    rfl
  have hLcov : (L zh).1.1 p = (L z).1.1 q := by
    calc
      (L zh).1.1 p = (translateFullJet i h (z : FullJet T)).1.2 p -
          ∑ j : Fin 3,
            (translateFullJet i h (z : FullJet T)).1.1.1.2.2 p
              (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
            rw [hLvalue zh p, hzh]
      _ = (z : FullJet T).1.2 q - ∑ j : Fin 3,
          (z : FullJet T).1.1.1.2.2 q
            (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := hfullResidual z p
      _ = (L z).1.1 q := (hLvalue z q).symm
  have hfhval : fh.1.1 p = f.1.1 q := by
    rw [hfh]
    rfl
  constructor
  · constructor
    ·
      rw [hPfactor, hbval]
      exact (heq q).1.1
    ·
      rw [hPfactor, hbval]
      exact (heq q).1.2
  · calc
      (L zh).1.1 p = (L z).1.1 q := hLcov
      _ = f.1.1 q + principalPart (b.1 q - 1) ((H0 + G z).1 q) +
          B (b.1 q) (b.1 q) ((v + Q z).1 q) ((v + Q z).1 q) := (heq q).2
      _ = fh.1.1 p + principalPart ((translateForcingJet i h b).1 p - 1)
          ((translateForcingJet i h H0 + G zh).1 p) +
          B ((translateForcingJet i h b).1 p) ((translateForcingJet i h b).1 p)
            ((translateForcingJet i h v + Q zh).1 p)
            ((translateForcingJet i h v + Q zh).1 p) := by
            rw [← hfhval, ← hbval, ← hHcov, ← hvcov]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AffineRationalSolutionTranslation
