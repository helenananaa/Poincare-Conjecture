import PoincareConjecture.ParallelImplementation.BoundedClassicalHeatUniqueness
import PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
import PoincareConjecture.ParallelImplementation.FullJetSpatialTranslation
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SameWitnessHeatTranslation
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
/-- The originally chosen heat right inverse is a left inverse and commutes
with actual spatial translations on the same graph spaces and operators. -/
theorem same_witness_heat_inverse_translation
    (T alpha : ℝ) (hT : 0 < T)
    (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T))
    (hX : (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha)
    (hY : (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le)
    (L : Y →L[ℝ] X) (D : X →L[ℝ] Y)
    (hLD : L.comp D = ContinuousLinearMap.id ℝ X)
    (hLvalue : ∀ z : Y, ∀ p : Slab T,
      (L z).1.1 p = z.1.1.2 p - ∑ j : Fin 3,
        z.1.1.1.1.2.2 p (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) :
    Function.Injective L ∧ D.comp L = ContinuousLinearMap.id ℝ Y ∧
    (∀ z : Y, ‖z‖ ≤ ‖D‖ * ‖L z‖) ∧
    (∀ (i : Fin 3) (h : ℝ) (x xh : X),
      xh.1 = translateForcingJet i h x.1 →
      (D xh).1 = translateFullJet i h (D x).1) :=
/- SWARM_PROOF_BEGIN -/
by
  have hzero (z : Y) (hzL : L z = 0) : z = 0 := by
    apply Subtype.ext
    let w : FullJet T := z.1
    have hwmem : w ∈ fullParabolicJetSet T alpha hT.le := by
      have hzmem : w ∈ (Y : Set (FullJet T)) := by
        change z.1 ∈ (Y : Set (FullJet T))
        exact z.2
      rw [hY] at hzmem
      exact hzmem
    have hheat (p : Slab T) : w.1.2 p = ∑ j : Fin 3,
        w.1.1.1.2.2 p (EuclideanSpace.single j 1)
          (EuclideanSpace.single j 1) := by
      have hformula := hLvalue z p
      have hres : z.1.1.2 p - ∑ j : Fin 3,
          z.1.1.1.1.2.2 p (EuclideanSpace.single j 1)
            (EuclideanSpace.single j 1) = 0 := by
        calc
          _ = (L z).1.1 p := hformula.symm
          _ = 0 := by simp [hzL]
      change z.1.1.2 p = ∑ j : Fin 3,
        z.1.1.1.1.2.2 p (EuclideanSpace.single j 1)
          (EuclideanSpace.single j 1)
      exact sub_eq_zero.mp hres
    exact PoincareConjecture.ParallelImplementation.BoundedClassicalHeatUniqueness.zero_initial_heat_jet_eq_zero
      T alpha hT w hwmem hheat
  have hLinj : Function.Injective L := by
    intro z w hzw
    have hsub : L (z - w) = 0 := by
      rw [map_sub, hzw, sub_self]
    have hzero' := hzero (z - w) hsub
    have hval : (z - w).1 = 0 := congrArg Subtype.val hzero'
    apply Subtype.ext
    exact sub_eq_zero.mp (by simpa using hval)
  have hLDapply (x : X) : L (D x) = x := by
    have hh := congrArg (fun f : X →L[ℝ] X => f x) hLD
    simpa using hh
  have hDL : D.comp L = ContinuousLinearMap.id ℝ Y := by
    apply ContinuousLinearMap.ext
    intro z
    apply hLinj
    have hh := congrArg (fun f : X →L[ℝ] X => f (L z)) hLD
    simpa using hh
  have hbound : ∀ z : Y, ‖z‖ ≤ ‖D‖ * ‖L z‖ := by
    intro z
    have hz : D (L z) = z := hLinj (hLDapply (L z))
    calc
      ‖z‖ = ‖D (L z)‖ := by rw [hz]
      _ ≤ ‖D‖ * ‖L z‖ := D.le_opNorm _
  have htranslation : ∀ (i : Fin 3) (h : ℝ) (x xh : X),
      xh.1 = translateForcingJet i h x.1 →
      (D xh).1 = translateFullJet i h (D x).1 := by
    intro i h x xh hxh
    let z : FullJet T := (D x).1
    have hprops := full_jet_translation_properties T alpha hT.le i h
    have hzmem : z ∈ fullParabolicJetSet T alpha hT.le := by
      have hzY : z ∈ (Y : Set (FullJet T)) := by
        change (D x).1 ∈ (Y : Set (FullJet T))
        exact (D x).2
      rw [hY] at hzY
      exact hzY
    have hztranslated : translateFullJet i h z ∈
        fullParabolicJetSet T alpha hT.le := (hprops.1 z).2 hzmem
    have hztranslatedY : translateFullJet i h z ∈ (Y : Set (FullJet T)) := by
      rw [hY]
      exact hztranslated
    let ztranslated : Y := ⟨translateFullJet i h z, hztranslatedY⟩
    have hxres (q : Slab T) : x.1.1 q =
        z.1.2 q - ∑ j : Fin 3,
          z.1.1.1.2.2 q (EuclideanSpace.single j 1)
            (EuclideanSpace.single j 1) := by
      have hformula := hLvalue (D x) q
      rw [hLDapply x] at hformula
      exact hformula
    have hvalues (p : Slab T) : (L ztranslated).1.1 p = xh.1.1 p := by
      have hcov := hprops.2.2.2.2.2 z p
      calc
        (L ztranslated).1.1 p =
            (translateFullJet i h z).1.2 p - ∑ j : Fin 3,
              (translateFullJet i h z).1.1.1.2.2 p
                (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) :=
          hLvalue ztranslated p
        _ = z.1.2
              (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
                p i h) - ∑ j : Fin 3,
              z.1.1.1.2.2
                (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
                  p i h)
                (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := hcov
        _ = (translateForcingJet i h x.1).1 p := by
          change z.1.2
              (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
                p i h) - ∑ j : Fin 3,
              z.1.1.1.2.2
                (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
                  p i h)
                (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) =
            x.1.1
              (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
                p i h)
          exact (hxres
            (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
              p i h)).symm
        _ = xh.1.1 p := by rw [← hxh]
    have hLtranslated : L ztranslated = xh := by
      apply Subtype.ext
      apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
        T alpha (L ztranslated).1 xh.1
      · rw [← hX]
        exact (L ztranslated).2
      · rw [← hX]
        exact xh.2
      · exact hvalues
    have hLxh : L (D xh) = xh := hLDapply xh
    have hsame : L (D xh) = L ztranslated := by rw [hLxh, hLtranslated]
    have hDtranslated : D xh = ztranslated := hLinj hsame
    have hval := congrArg Subtype.val hDtranslated
    simpa [ztranslated, z] using hval
  exact ⟨hLinj, hDL, hbound, htranslation⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SameWitnessHeatTranslation
