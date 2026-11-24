import YM.Integration.WilsonCoherentTerminalFrame
import YM.Integration.WilsonReportingPrescribedOldSource

/-! The two full signed coefficient vectors in the same finite direct sum of
original Wilson section coordinates, before any positive measure is selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldCoordinates
open Function Finset Lattice Wilson RG Tree Precision Source Labels
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open Extraction Table Spec RG17 MS MS.Menus MS.Local.Physical
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {B : Deck G} (Q : MS.Land.Prescription B)
  (u : MS.Rake.Label B)

/-- One independent coordinate for every engineering size and every original
section index of that size. -/
abbrev Panel (h : ℕ) := (a : Fin (h+1))→R.family.label a.val

def prescribed (μ : ℝ) (k : ℕ) : Panel R u.h := fun a=>
  ∑j : Fin (a.val+1),∑b : B.BIndex a.val j.val,
    oil (Q.fees u.h u.item) (⟨a,j,b⟩ : Glyph B u.h) k μ •
      ActualOriginalDictionary.coordinates R B a.val j.val b

variable {f : Extraction.Order} {S : Table R.family.book} {F : Spec.Final R.family f S} (L : Layout F)
  {h N per : ℕ} (o : Site (R.family.side N per)) (U : Config G (R.family.side N per))

def slot (a : ℕ) : R.family.label a →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval (entry (expandAt o U))).toLinearMap.comp (R.family.localSection a).evalC

def read (v : Panel R h) : ℂ := ∑a,(slot R o U a.val) (v a)

def reported (r : ℝ) (N per : ℕ) (w : Panel R h) (α : Fin (h+1)→ℂ) : Panel R h := fun a=>
  α a • WilsonCoherentTerminalFrame.coordinates R N per (atRef L a.val r (N,per) (w a))

theorem independent (μ : ℝ) (k : ℕ) :
    ActualOriginalCalibratedColumns.weightedObservable R B Q u μ (R.family.side N per) o U k =
      read R o U (prescribed R Q u μ k) := by
  rw [ActualOriginalCalibratedColumns.weighted_observable_original]
  unfold read prescribed
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro a _
  rw [Fintype.sum_sigma,map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_sum]
  apply sum_congr rfl
  intro b _
  rw [map_smul]
  rfl

theorem measured (r : ℝ) (w : Panel R h) (α : Fin (h+1)→ℂ) :
    (∑a,α a*R.family.O N per (atRef L a.val r (N,per) (w a)) o U)=
      read R o U (reported R L r N per w α) := by
  unfold read reported
  apply sum_congr rfl
  intro a _
  rw [map_smul]
  congr 1
  let v := atRef L a.val r (N,per) (w a)
  have law := Descent.field_label_correct (C:=R.family) (N:=N) (p:=per) (o:=o)
    (WilsonCoherentTerminalFrame.coordinates R N per v)
  rw [WilsonCoherentTerminalFrame.named R N per v] at law
  exact congrFun law U

/-- The discrepancy is read directly in the common original stencil basis.
The physical mesh, threshold, every lower fee and all complex signs remain. -/
theorem original (r μ : ℝ) (k : ℕ) (w : Panel R u.h) (α : Fin (u.h+1)→ℂ) :
    (∑a,α a*R.family.O N per (atRef L a.val r (N,per) (w a)) o U)-
      ActualOriginalCalibratedColumns.weightedObservable R B Q u μ (R.family.side N per) o U k =
      read R o U (reported R L r N per w α-prescribed R Q u μ k) := by
  rw [measured R L o U,independent R Q u o U]
  unfold read
  rw [←sum_sub_distrib]
  exact sum_congr rfl fun a _=>(map_sub (slot R o U a.val) _ _).symm

end YM.Integration.WilsonReportingPrescribedOldCoordinates
