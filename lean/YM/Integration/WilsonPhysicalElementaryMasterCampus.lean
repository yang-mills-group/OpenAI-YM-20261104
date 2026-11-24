import YM.Integration.WilsonPhysicalElementaryPaidHearing
import YM.Integration.WilsonPhysicalRestrictedCampus

/-! Restrict the previously appointed public programme to a simultaneous choice of
elementary detecting fields. The duplicate subjects retain their common real home,
original f and K, and the finite inverse issued by the parent school. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalElementaryMasterCampus
open Function Filter Finset MeasureTheory Lattice RG Wilson Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonPhysicalElementaryPaidHearing (Axes heads)
open WilsonPhysicalElementarySourceSpindle (Roster)
open WilsonMovingForkOpticalBook (reporter)
open RG17 PhysMS EveryPhase OPE.Orbits OPE.Log
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family order S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
variable (J:ℝ→tower S)(Z:WilsonPrescription G){n D T:ℕ}(d:Fin n→Fin (D+1))
    (x:∀i,RG17.Free R.family (d i).val){δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val)

def master:=WilsonReflectedMixedMasterSchool.field F J Z D T (fun w:Roster (R:=R) d=>d w.1)
  (fun w=>WilsonPhysicalVaneBasis.field R.family (d w.1) w.2) (fun w=>x w.1) books

def choice (a:Axes (R:=R) d)(i:Fin n):Roster (R:=R) d:=⟨i,a i⟩

theorem original [Nonempty (Fin n)] {t:ℕ}{e E:Roster (R:=R) d→ℕ}{M:Roster (R:=R) d→ℝ}
    {tuition:ℝ}{power target:ℕ}{ρ:Fin n→{s:ℝ//0<s ∧ s<δ}}{K:ℕ}
    (paid:School F D T t (fun w:Roster (R:=R) d=>d w.1) e books (master F J Z d x books) M E
      tuition power target (fun w=>ρ w.1) (reporter F books (fun w:Roster (R:=R) d=>ρ w.1)) K)
    (a:Axes (R:=R) d):
    School F D T t d (fun i=>e (choice d a i)) books (heads F J Z d x books a)
      (fun i=>M (choice d a i)) (fun i=>E (choice d a i)) tuition power target ρ (reporter F books ρ) K:=by
  rw [WilsonPhysicalElementarySourceSpindle.reporter_eq F d books ρ] at paid
  exact WilsonPhysicalRestrictedCampus.original F paid (choice d a)

end YM.Integration.WilsonPhysicalElementaryMasterCampus
