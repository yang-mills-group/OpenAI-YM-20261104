import YM.Integration.WilsonPositionOriginalDiagnosticPurse
import YM.Integration.WilsonPositionThermometerGradedBirth
import YM.Integration.WilsonPositionThermometerCapStation
import YM.AllOrder.Leading.Solve

/-! The scalar and all higher diagnostic words use their intrinsic grades, even
when a single position screen was presented at the top horizon. One original
station supplies the signed cutoff representative for each of these grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticGrades
open Function Filter Set Finset Metric MeasureTheory Extraction Table Spec OPE Climb PhysMS Maxwell
open Trace.Pilot XSpace XSpace.Normalize FVA2 MS MS.Local.Physical MS.Menus MS.Theater
open Lattice Wilson RG Marker Source FVA1 RG12 RG17 PhysicalNext.Repeat.Legato
open MergeProof MergeProof.East MergeProof.Accent MergeProof.Replicums
open Push.GridApprox.Nil OriginalForcedAddresses ActualRunUnmaskedPartners Next.UVStress Next.Rank
open WilsonPositionThermometerCapStation WilsonPositionOriginalDiagnosticPanel WilsonPositionOriginalDiagnosticRead
open scoped Topology BigOperators Classical
variable {G:Gauge} (B:Deck G) {d n H:ℕ}

def atGrade (a:Glyph B d) : Glyph B a.size := ⟨Fin.last a.size,a.2⟩

def leg (C:Family G) (a:Glyph B d) : RG17.Free C a.size :=
  (Maxwell.Free.fields C.labels a.size).symm ((Daylight B a.size) (atGrade B a))

theorem promoted (C:Family G) (a:Glyph B d) :
    (Maxwell.Free.scheme C.labels).rise (Nat.le_of_lt_succ a.1.isLt) (leg B C a) =
      (Maxwell.Free.fields C.labels d).symm ((Daylight B d) a) := by
  apply Maxwell.Free.address_inj C.labels d
  rw [Maxwell.Free.address_rise,leg,Maxwell.Free.address_eval,Maxwell.Free.address_eval,
    LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,readHeight,readHeight]
  rfl

variable {R:Run G} {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S) (J:ℝ→PhysMS.tower S)

theorem point (lead:PhysMS.Leading F J) (d:ℕ) : ∀ᶠ r in Trace.Pilot.trail,
    ∀ {n:ℕ} (a:Fin n→Glyph B d) (x:Points n), x∈conf n →
    measured F none (J r) (d:=fun _ : Fin n=>d)
      (fun i=>(Maxwell.Free.fields R.family.labels d).symm ((Daylight B d) (a i))) r x =
    measured F none (J r) (d:=fun i=>(a i).size) (fun i=>leg B R.family (a i)) r x := by
  have rises:=Filter.eventually_all.mpr (fun a:Glyph B d=>lead.raised (Nat.le_of_lt_succ a.1.isLt))
  filter_upwards [rises,RG17.positiveLength] with r at_r positive n a x hx
  change S.classMoment S _ (r • x) _ = _
  simp_rw [←promoted B,at_r]
  exact AllOrder.Leading.moment_inclusion F.room.kernel.laws.toSymmetric F.phase.transport.injection
    (fun i=>Nat.le_of_lt_succ (a i).1.isLt) (Work.A05.smul_conf positive hx)
    (fun i=>J r (a i).size (leg B R.family (a i)))

theorem tested (lead:PhysMS.Leading F J) (d:ℕ) : ∀ᶠ r in Trace.Pilot.trail,
    ∀ (w:Window G d) (a:Fin w.n→Glyph B d),
    WilsonPositionOriginalDiagnosticRead.reading B (WilsonPositionPrescribedScreen.hierarchy F J d r) w a =
      w.t.applyTo (measured F none (J r) (d:=fun i=>(a i).size) (fun i=>leg B R.family (a i)) r) := by
  filter_upwards [point B F J lead d,RG17.positiveLength] with r at_r positive w a
  unfold WilsonPositionOriginalDiagnosticRead.reading
  rw [WilsonPositionPrescribedScreen.actual F J _ _ _ _ positive]
  exact w.t.apply_eq fun x hx=>at_r a x hx

variable (A:Group R.family H) (fit:d≤H)

/-- True top representatives of the graded sections, formed on one station
and thus one original ultraviolet/period pair, with arbitrary deposited weights. -/
def upperIndex (a:Glyph B d) : Fin (H+1) := ⟨a.size,lt_of_lt_of_le a.1.isLt (Nat.add_le_add_right fit 1)⟩

def upper (a:Glyph B d) (z:UVIndex) : R.family.label a.size :=
  A.station.wheel.atCut z (index A (upperIndex B fit a)) (A.change (upperIndex B fit a) (leg B R.family a))

def date (a:Glyph B d) : Fin (A.horizon+1) := index A (upperIndex B fit a)

def originalVector (a:Glyph B d) : (Bel R.family.book).Field (date B A fit a) :=
  A.change (upperIndex B fit a) (leg B R.family a)

/-- The reference dates needed by GradedBirth.original for this very station are
paid before choosing the ultraviolet, period, placements or diagnostic projections. -/
theorem eligible {N:ℕ} (age:entrance R B d ≤ N) (a:Fin n→Glyph B d) :
    ∀ i, R.family.ref (date B A fit (a i)) ≤ N := fun i=>
  (le_sup (s:=univ) (f:=fun u:Glyph B d=>R.family.ref u.size) (mem_univ (a i))).trans age

end YM.Integration.WilsonPositionOriginalDiagnosticGrades
