import YM.Integration.WilsonPositionOriginalDiagnosticCells
import YM.Integration.WilsonPositionOriginalDiagnosticGrades

/-! On the selected position hierarchy, each signed test in the nonlinear
field normalization is heard on the one original graded Wilson cohort. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticHearing
open Function Filter Set Finset Metric MeasureTheory Extraction Table Spec Climb PhysMS Maxwell
open Trace.Pilot XSpace XSpace.Normalize MS MS.Local.Physical MS.Menus MS.Theater
open Lattice Wilson RG Marker Source FVA1 RG12 RG17 PhysicalNext.Repeat.Legato
open MergeProof.East Next.UVStress Next.Rank Spin
open WilsonPositionThermometerCapStation WilsonPositionOriginalDiagnosticGrades
open WilsonPositionOriginalDiagnosticRead WilsonPositionPhysicalCellTest
open scoped Topology BigOperators Classical
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S)
    {Y:Ultrafilter UVIndex} (hl:(Y:Filter UVIndex)≤f.fuse)
    {c d:ℕ} (A:ℝ→Group R.family c) (fit:d≤c) (B:Deck G)

def stock (r:ℝ) (a:Glyph B d) : R.family.label a.size :=
  (A r).lift (date B (A r) fit a) (originalVector B (A r) fit a)

private theorem current (r:ℝ) (a:Glyph B d)
    (sw:Tendsto (A r).station.wheel.atCut (Y:Filter UVIndex) (𝓝 (A r).lift)) :
    Tendsto (upper B (A r) fit a) (Y:Filter UVIndex) (𝓝 (stock A fit B r a)) := by
  let j:=date B (A r) fit a
  let v:=originalVector B (A r) fit a
  have look:Continuous (fun l:Lifts R.family (A r).horizon=>l j) := continuous_apply j
  have act:Continuous (fun l:(Bel R.family.book).Field j →L[ℂ] R.family.book.Ref j=>l v) :=
    (ContinuousLinearMap.apply ℂ _ v).continuous
  exact (act.comp look).continuousAt.tendsto.comp sw

variable (simple:G.Simple) (H:(Bel R.family.book).Hierarchy) (lead:PhysMS.Leading F J)
variable {I:Type} (j:I→Fin (c+1)) (v:∀ a,(Bel R.family.book).Field (j a)) (m:ℕ)
variable (hgroup:∀ᶠ r in trail, projects (f:=f) (Y:=Y) H j v (A r) (J r) m r)

include H j v m lead hgroup in
private theorem registered : ∀ᶠ r in trail, ∀ (w:Window G d) (a:Fin w.n→Glyph B d),
    w.t.applyTo (fun x=>S.value (fun i=>(a i).size) (r•x) (fun i=>stock A fit B r (a i))) =
      WilsonPositionOriginalDiagnosticRead.reading B (WilsonPositionPrescribedScreen.hierarchy F J d r) w a := by
  filter_upwards [hgroup,tested B F J lead d,RG17.positiveLength] with r at_r target positive w a
  rw [target w a]
  apply w.t.apply_eq
  intro x hx
  change S.value (fun i=>(a i).size) (r•x) _= S.classMoment S _ (r•x) _
  have field (i:Fin w.n) : J r (a i).size (leg B R.family (a i)) = S.project (a i).size (stock A fit B r (a i)) :=
    ((at_r.2.2.2.2.1 (upperIndex B fit (a i))).2.2 (leg B R.family (a i)))
  simp_rw [field]
  exact (S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl)
    (Work.A05.smul_conf positive hx) (fun i=>⟨(a i).size,stock A fit B r (a i)⟩)).symm

include hl simple H j v m lead hgroup in
theorem original : ∀ᶠ r in trail, ∀ (w:Window G d) (a:Fin w.n→Glyph B d),
    Tendsto (fun z=>w.t.applyTo (WilsonPositionOriginalDiagnosticCells.cut (R:=R) (fun i=>(a i).size)
      (fun z i=>upper B (A r) fit (a i) z) r z)) (Y:Filter UVIndex)
      (𝓝 (WilsonPositionOriginalDiagnosticRead.reading B (WilsonPositionPrescribedScreen.hierarchy F J d r) w a)) := by
  filter_upwards [registered F J A fit B H lead j v m hgroup,hgroup,RG17.positiveLength] with r equals ready positive w a
  rw [←equals w a]
  exact WilsonPositionOriginalDiagnosticCells.signed F (fun i=>(a i).size) w.t
    (fun z i=>upper B (A r) fit (a i) z) (fun i=>stock A fit B r (a i)) simple hl positive
    (fun i=>current A fit B r (a i) ready.2.2.2.1)

include H j v m lead hgroup in
theorem ordered : ∀ᶠ r in trail, ∀ (hr:0<r) (w:Window G d) (a:Fin w.n→Glyph B d),
    f.limits (fun p=>suitable R.family.S p (dilate hr w.t))
      (fun N p=>(R.family.S.a N:ℂ)^(4*w.n)*∑ x:Sites R (N,p) w.n,
        dilate hr w.t (Extraction.Order.cells R.family N p x) *
        R.family.ensemble (N:=N) (p:=p) (fun i=>(a i).size) x (fun i=>stock A fit B r (a i)))
      (WilsonPositionOriginalDiagnosticRead.reading B (WilsonPositionPrescribedScreen.hierarchy F J d r) w a) := by
  filter_upwards [registered F J A fit B H lead j v m hgroup] with r equals hr w a
  rw [←equals w a]
  exact WilsonPositionOriginalDiagnosticCells.ordered F (fun i=>(a i).size) w.t (fun i=>stock A fit B r (a i)) hr

end YM.Integration.WilsonPositionOriginalDiagnosticHearing
