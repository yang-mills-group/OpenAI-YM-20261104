import YM.Integration.WilsonPositionScaleLawGuardCarry

/-! The original fixed field, in its top grade, obeys the true independent MS scale transition at each prescribed order on the whole half interval. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardTopStep
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize Asymptotics
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawGuardPhysical (expected)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGrade (grade)
open WilsonPositionScaleLawGuardCarry (term)
open scoped Topology Classical Asymptotics
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
def column (d:ℕ)(r:ℝ)(O:S.Field d):=grade R.family (Fin.last d) (physical F J Z d r O)

include H in
theorem exactRow (d Q:ℕ)(O:S.Field d)(w:ℝ×Ratio):
    grade R.family (Fin.last d) (term Z M ν F J d Q O w)=
      column Z F J d w.1 O-expected F J Z M ν d Q w.1 w.2 (column Z F J d (w.2.val*w.1) O):=by
  let P:=grade R.family (Fin.last d)
  let x:=physical F J Z d w.1 O
  let y:=physical F J Z d (w.2.val*w.1) O
  let U:=dressed Z F J d w.1 w.2
  let N:=expected F J Z M ν d Q w.1 w.2
  have gear:P (U y)=P x:=by
    simpa only [Fin.val_last,Nat.sub_self,pow_zero,one_smul] using (WilsonPositionScaleLawGuardOrbit.step F J Z w.1 w.2 (Fin.last d) O)
  have homogeneous:P (N y)=N (P y):=WilsonPositionScaleLawGuardDiagonal.original R.family Z M H ν _ (Fin.last d) Q _ y
  change P (U y-N y)=P x-N (P y)
  rw [P.map_sub,gear,homogeneous]

include H in
theorem original (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:WilsonPositionScaleLawGuardLittle.scale F J Z M ν d 2):
    ∃p:ℕ,∀q:ℕ,WilsonPositionScaleLawGuardLittle.scale F J Z M ν d (q+2*p)→∀O:S.Field d,
      (fun w:ℝ×Ratio=>column Z F J d w.1 O-
        expected F J Z M ν d (q+2*p) w.1 w.2 (column Z F J d (w.2.val*w.1) O))=o[sweep] (fun w=>gθ w.1^q):=by
  obtain ⟨p,invoice⟩:=WilsonPositionScaleLawGuardCarry.original Z M H ν F J d funded law
  refine ⟨p,?_⟩;intro q paid O
  have charged:=WilsonPositionScaleLawGuardCarry.mapped (grade R.family (Fin.last d)) _ _ (invoice q paid O)
  exact charged.congr (exactRow Z M H ν F J d (q+2*p) O) (fun _=>rfl)

end YM.Integration.WilsonPositionScaleLawGuardTopStep
