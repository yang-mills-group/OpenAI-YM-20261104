import YM.Integration.WilsonThermometerWeakPairAxes
import YM.Integration.WilsonMacroscopicFundedReader

import YM.Integration.WilsonMatrixTicketLanesStrongSeed
import YM.Integration.WilsonMatrixTicketLanesRetained
import YM.Integration.WilsonMatrixTicketLanes
import YM.Integration.WilsonMatrixTicketLanesChargeSource
import YM.Integration.WilsonMacroscopicSharpPacket

/-! Preserve the ordinary moving detector expense on exactly the funded original
sector, together with the calendar, coupling orientation and observer already
issued by the original matrix reconstruction. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerWeakPairSector
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)

open OPE.Orbits OPE.Arboreal Table XSpace XSpace.Normalize PhysMS.Frame
open WilsonThermometerWeakMovingCorner WilsonThermometerWeakPairClock
open scoped Matrix.Norms.Frobenius
local notation "child" => WilsonThermometerWeakPairRooms.near
local notation "sites" => WilsonThermometerWeakPairFork.position

def Salary {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(J:ℝ→PhysMS.tower S):Prop:=
  ∀(_V:Store G)(g:ℝ→ℝ),Coupling G g→∀ (I:Type)[Fintype I](d:I→↥child→ℕ)(e:I→ℕ)(h:ℕ)
    (v:∀i j,RG17.Free R.family (d i j))(w:∀i,RG17.Free R.family (e i))(view:I→Viewers F)(M δ:ℝ),0≤M→0<δ→
    ∃K:ℕ,∀(o:ℕ)(ε:ℝ),0<ε→∀B:ℕ,K+o+1≤B→∀ᶠ r in trail,let t:=scale g B r
      ∀(i:I)(x y z:E4),‖x‖≤M → ‖y‖≤M → ‖z‖≤M → 2*δ≤‖z‖ → δ≤‖x-y‖ →
        ‖formula F Q (crop (sites r t x y z) child) 0 (born J r (v i)) (sole (t • z))
          (sole ((WilsonThermometerWeakMovingCorner.far F J (e i) t (w i)).2):Labels S (fun _:Unit=>e i)) h (view i)‖≤ε*(g r)^o*(r/t)^h

/-- All orders use a single reader, limit law, charged program and field hierarchy
    for each original extraction order. -/
def Elected (cohort:Ultrafilter (ℕ×ℕ)→Prop):Prop:=
  ∀v:Extraction.Order,∃(w:Extraction.Order)(S:Table R.family.book)
    (F:Final R.family (v.refine w) S)(L:EveryPhase.Almanac F)
    (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin),
    EveryPhase.Completed F L ∧ Trace.Target.Result.{u} F simple ∧ Trace.Target.Exclusion.{u} F ∧
    Facilities R.family (v.refine w) S ∧ Orbits.Foundation F Q ∧ SingleLog F Q.port ∧
    ∃(Y:(Bel R.family.book).Hierarchy)(Z:Trace.Terrace.Arch R.family)(l:Ultrafilter (ℕ×ℕ))
      (_bliss:Bliss F l Z Y)(P P':ℝ→Spin.change S 4)(J:ℝ→PhysMS.tower S)
      (φ:E4→ℝ)(a d e:ℝ→ℝ), (∀ᶠr in trail,J r 4=P' r) ∧
      Trace.Target.XScheme F simple Y l P P' φ ∧ Trace.Target.FieldComparison F Y Z P P' a d e ∧
      Leading F J ∧ (∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d) ∧
      (l:Filter (ℕ×ℕ)) ≤ (v.refine w).fuse ∧ cohort l ∧
      Log.MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter (ℕ×ℕ)) ∧ Salary F Q J

theorem original {T:Campaign R} (W:Campaign.Pillars R T) {κ:ℝ}
    (fund:FundedOriginalProperties.{u} simple κ W)
    (physical:WilsonMatrixTicketFuelPrice.FromStrongBin R.family)
    (cohort:Ultrafilter (ℕ×ℕ)→Prop)
    (issued:∀(f:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤f.fuse→cohort l):
    Elected.{u} R simple cohort:=by
  intro v
  obtain ⟨w,A,rows,B,z,tr,S,E,projected,base,⟨seed⟩,strong,_⟩:=
    WilsonMatrixTicketLanesStrongSeed.original R simple v
  obtain ⟨F,X,L,Q,_,_,done,trace,omitLaw,fac,foundation,_,_,_⟩:=
    WilsonMatrixTicketLanesRetained.original simple W fund (v.refine w) base seed
  have lanes:=physical (v.refine w) A rows B z tr S E F projected base strong fac.toServices
  obtain ⟨Y,Z,l,bliss,P,P',J,φ,a,d,e,grade,scheme,comp,lead,obedient⟩:=
    Frame.meter_found.{u} simple F trace
  have bill:=WilsonMatrixTicketLanes.on_ultrafilter lanes l bliss.lies
  refine ⟨w,S,F,L,Q,done,trace,omitLaw,fac,foundation,first_log F fac bliss.lies bill Q.spans,
    Y,Z,l,bliss,P,P',J,φ,a,d,e,grade,scheme,comp,lead,obedient,bliss.lies,issued _ _ bliss.lies,bill,?_⟩
  intro V g hg I _ d e h v₀ w₀ view M δ mn dp
  exact WilsonThermometerWeakPairAxes.original F fund L done fac (fun U hu=>WilsonMatrixTicketLanes.on_ultrafilter lanes U hu) Q foundation J V lead g hg d e h v₀ w₀ view mn dp

theorem previous (cohort:Ultrafilter (ℕ×ℕ)→Prop)(sale:Elected.{u} R simple cohort):
    WilsonMacroscopicFundedReader.Elected.{u} R simple cohort:=by
  intro v
  obtain ⟨w,S,F,L,Q,done,trace,exc,fac,book,nested,Y,Z,l,bliss,P,P',J,φ,a,d,e,grade,scheme,comp,lead,obedient,below,charged,ticket,_⟩:=sale v
  exact ⟨w,S,F,L,Q,done,trace,exc,fac,book,nested,Y,Z,l,bliss,P,P',J,φ,a,d,e,grade,scheme,comp,lead,obedient,below,charged,ticket⟩

end YM.Integration.WilsonThermometerWeakPairSector

