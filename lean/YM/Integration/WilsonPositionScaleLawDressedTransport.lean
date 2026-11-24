import YM.Integration.WilsonPositionScaleLawWholeHome
import YM.Integration.WilsonPositionScaleLawIndependent
import YM.FVA2.Clef.Winds

/-! The exact two original cocycles and the independent homogeneous scale guard.
The same dimensional correction is fixed before the requested precision. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawDressedTransport
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPositionScaleLawHome (positioned Ratio)
open WilsonPositionScaleLawNative (exactOp positive)
open scoped Topology Classical BigOperators

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

abbrev guard (s:ℝ)(d:ℕ):Guard G d:=GroupS.gaugeN Z.scheme Z.criterion M ν s d
abbrev adjust (d:ℕ):Guard G d:=Measure.adjust Z.scheme Z.criterion d

include H in
theorem published (s:ℝ)(d:ℕ):
    convertT s (adjust Z d)*guard Z M ν s d=
    GroupS.gaugeB Z.criterion M ν s d*Reg.Point.stepV (GroupS.ψ Z.criterion M ν s) (adjust Z d):=by
  let mission:=H.details.toServed.toPosted.toQuoted.toContract
  rw [guard,Clef.originate hG mission ν]
  exact Clef.freeze (fun i=>Clef.real (d:=i) mission ν) s d

include H in
theorem native (s:ℝ)(d:ℕ):Native (guard Z M ν s d):=by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact GroupS.fitsN ν Z.scheme Z.criterion M σ hG data.Taylor data.still data.base s

include H in
theorem graded (s:ℝ)(d k:ℕ)(i:Fin (d+1))(p:Sec G d):
    Level.proj i (coeff k (guard Z M ν s d) (Level.proj i p))=
    coeff k (guard Z M ν s d) (Level.proj i p):=
  (Level.graded_test _).mp (native Z M H ν s d k) p i

include H in
theorem inclusion (s:ℝ){d e:ℕ}(h:d≤e):Walk h (guard Z M ν s d) (guard Z M ν s e):=by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact GroupS.walkN ν Z.scheme Z.criterion M σ hG data.Taylor data.still data.base s h

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

def dressed (d:ℕ)(r:ℝ)(t:Ratio):E d→L[ℂ]E d:=
  WilsonPhysicalPositionUniformBranches.change (WilsonPositionHomogeneousFrame.homogeneous F J Z) d r t.val (positive t)

theorem original (d:ℕ)(r:ℝ)(t:Ratio)(v:E d):
    WilsonPositionHomogeneousFrame.change F J Z d r
      (Pert.Scale.gear R.family.labels d t.val (dressed Z F J d r t v))=
    Pert.Scale.gear R.family.labels d t.val (exactOp F J Z.store d (r,t)
      (WilsonPositionHomogeneousFrame.change F J Z d (t.val*r) v)):=by
  apply (positioned F J Z.store r d).injective
  calc
    _=WilsonPositionHomogeneousFrame.homogeneous F J Z (t.val*r) d v:=
      Frame.cocycle_value d (WilsonPositionHomogeneousFrame.homogeneous F J Z) v t.val r (positive t)
    _=_:=(Frame.cocycle_value d (positioned F J Z.store) (WilsonPositionHomogeneousFrame.change F J Z d (t.val*r) v)
      t.val r (positive t)).symm

end YM.Integration.WilsonPositionScaleLawDressedTransport
