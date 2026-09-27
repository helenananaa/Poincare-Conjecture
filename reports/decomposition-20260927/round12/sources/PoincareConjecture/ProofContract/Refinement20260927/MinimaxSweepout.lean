import PoincareConjecture.ProofContract.Refinement20260927.AcceptedSeventeen
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set Filter V1
open scoped Topology
abbrev SweepParameter := Icc (0 : ℝ) 1
/-- **Math.** An abstract nonnegative sweepout-energy spectrum, not yet the
geometric Dirichlet energy of a homotopy class. Real geometry must supply that
identification. Width is DEFINED by infimum of slice suprema, not a free field. -/
structure SweepoutSpectrum where
  index : Type u
  nonempty : Nonempty index
  energy : index → ℝ → SweepParameter → ℝ
  nonneg : ∀ i t x, 0 ≤ energy i t x
  bounded : ∀ i t, BddAbove (range (energy i t))
instance (F : SweepoutSpectrum.{u}) : Nonempty F.index := F.nonempty
instance : Nonempty SweepParameter := ⟨⟨0,by norm_num⟩⟩
def SweepoutSpectrum.peak (F : SweepoutSpectrum.{u}) (i : F.index) (t : ℝ) : ℝ :=
  sSup (range (F.energy i t))
def SweepoutSpectrum.width (F : SweepoutSpectrum.{u}) (t : ℝ) : ℝ :=
  sInf (range (fun i => F.peak i t))
theorem SweepoutSpectrum.energy_le_peak (F : SweepoutSpectrum.{u}) (i : F.index) (t : ℝ)
    (x : SweepParameter) : F.energy i t x ≤ F.peak i t := le_csSup (F.bounded i t) ⟨x,rfl⟩
theorem SweepoutSpectrum.peak_nonneg (F : SweepoutSpectrum.{u}) (i : F.index) (t : ℝ) :
    0 ≤ F.peak i t := (F.nonneg i t (Classical.choice inferInstance)).trans (F.energy_le_peak i t _)
theorem SweepoutSpectrum.peaks_bddBelow (F : SweepoutSpectrum.{u}) (t : ℝ) :
    BddBelow (range (fun i => F.peak i t)) := ⟨0,by rintro _ ⟨i,rfl⟩; exact F.peak_nonneg i t⟩
theorem SweepoutSpectrum.width_nonneg (F : SweepoutSpectrum.{u}) (t : ℝ) :
    0 ≤ F.width t := le_csInf (range_nonempty _) (by rintro _ ⟨i,rfl⟩; exact F.peak_nonneg i t)
theorem SweepoutSpectrum.width_le_peak (F : SweepoutSpectrum.{u}) (i : F.index) (t : ℝ) :
    F.width t ≤ F.peak i t := csInf_le (F.peaks_bddBelow t) ⟨i,rfl⟩
/-- **Math.** A transfer sends EACH admissible before-sweepout to an admissible
after-sweepout, with pointwise energy control. It is not an assumed width jump. -/
structure SweepoutTransfer (F G : SweepoutSpectrum.{u}) (t : ℝ) where
  send : F.index → G.index
  reparam : F.index → SweepParameter → SweepParameter
  energy_le : ∀ i x, G.energy (send i) t x ≤ F.energy i t (reparam i x)
theorem SweepoutTransfer.width_le {F G : SweepoutSpectrum.{u}} {t : ℝ}
    (h : SweepoutTransfer F G t) : G.width t ≤ F.width t := by
  apply le_csInf (range_nonempty _)
  rintro _ ⟨i,rfl⟩
  apply (G.width_le_peak (h.send i) t).trans
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x,rfl⟩
  exact (h.energy_le i x).trans (F.energy_le_peak i t _)
#print axioms SweepoutSpectrum.energy_le_peak
#print axioms SweepoutSpectrum.peak_nonneg
#print axioms SweepoutSpectrum.width_nonneg
#print axioms SweepoutSpectrum.width_le_peak
#print axioms SweepoutTransfer.width_le
end PoincareConjecture.ProofContract.Refinement20260927
