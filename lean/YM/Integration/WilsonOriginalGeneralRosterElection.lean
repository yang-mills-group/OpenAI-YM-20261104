import YM.Integration.WilsonOriginalGeneralRosterSale
import YM.Integration.WilsonMeasuredPublicEntrancePublicFaculty

/-! The physical frame and its free/heterogeneous arm prescription are elected once.
Arity, menu, nominations, smooth tests, cutoff, period and programmed rows are all
subsequent queries on this same Wilson family and extraction. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterElection
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open RG RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedMixedMasterSchool (field)
open WilsonOriginalGeneralRosterSale (Register)
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{simple:G.Simple}

def Experiments {v:Extraction.Order}{S:Table R.family.book}(F:Final R.family v S)
    (l:Ultrafilter (ℕ×ℕ))(H:(Bel R.family.book).Hierarchy)(z:Trace.Terrace.Arch R.family)
    (J:ℝ→PhysMS.tower S):Prop:=
  ∀(I:Type)[Fintype I][Nonempty I](Z:WilsonPrescription G)(D:ℕ),
    ∃t≥D+3,∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
    (∀s,WilsonMovingForkWindowBooks.Priced F (books s)) ∧ ∀(h:ℕ)(d:I→Fin (D+1))
    (y:∀i,(Spin.comparator R.family.book).Field (d i).val)(x:∀i,RG17.Free R.family (d i).val),
    WilsonOriginalGeneralRosterSale.Register F books h t d (field F J Z D T d y x books)

theorem onFrame {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {T:Campaign R}{W:Campaign.Pillars R T}(paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R T W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels)
    (lamp:WilsonReportLampForecast.Ready R.family.path.levels)
    {v:Extraction.Order}{S:Table R.family.book}(F:Final R.family v S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    (J:ℝ→PhysMS.tower S)(bliss:Bliss F l z H)(lead:Leading F J)
    (obedient:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d):Experiments F l H z J:=by
  intro I _ _ Z D
  obtain ⟨t,td,T,δ,dp,books,amount,grant⟩:=WilsonMeasuredPublicEntrancePublicFaculty.onFrame
    paid F J bliss lead obedient I Z D
  refine ⟨t,td,T,δ,dp,books,amount,?_⟩
  intro h d y x
  exact WilsonOriginalGeneralRosterSale.original F books _ paid bank lamp bliss (grant h d y x)

def Elected (R:Run G)(simple:G.Simple)(cohort:Ultrafilter (ℕ×ℕ)→Prop)(v:Extraction.Order):Prop:=
  ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
    (L:EveryPhase.Almanac F)(Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:(Bel R.family.book).Hierarchy)(z:Trace.Terrace.Arch R.family)(l:Ultrafilter (ℕ×ℕ))(_ : Bliss F l z H)
    (P P':ℝ→Spin.change S 4)(J:ℝ→PhysMS.tower S)(φ:E4→ℝ)(a d e:ℝ→ℝ),
    EveryPhase.Completed F L ∧ Trace.Target.Result.{u} F simple ∧ Trace.Target.Exclusion.{u} F ∧
    Facilities R.family (v.refine w) S ∧ Orbits.Foundation F Q ∧ SingleLog F Q.port ∧
    (∀ᶠ r in trail,J r 4=P' r) ∧ Trace.Target.XScheme F simple H l P P' φ ∧
    Trace.Target.FieldComparison F H z P P' a d e ∧ Leading F J ∧
    (∀d,∀ᶠr in trail,Frame.obedient F H (J r) d) ∧
    (l:Filter (ℕ×ℕ))≤(v.refine w).fuse ∧ cohort l ∧
    Log.MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter (ℕ×ℕ)) ∧
    (∀D,∃t:ℕ,∀ᶠr in trail,∃j m,Pool F l r j m D (dock r^t)) ∧ Experiments F l H z J

theorem onRun {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {T:Campaign R}{W:Campaign.Pillars R T}(paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R T W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels)
    (lamp:WilsonReportLampForecast.Ready R.family.path.levels)(cohort:Ultrafilter (ℕ×ℕ)→Prop)
    (select:∀(v:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤v.fuse→cohort l)(v:Extraction.Order):
    Elected.{u} R simple cohort v:=by
  obtain ⟨w,S,F,L,Q,H,z,l,bliss,P,P',J,φ,a,d,e,completed,result,exclusion,fac,foundation,single,top,
    scheme,compare,leading,obedient,lies,selected,ticket,pool⟩:=paid.physical cohort select v
  exact ⟨w,S,F,L,Q,H,z,l,bliss,P,P',J,φ,a,d,e,completed,result,exclusion,fac,foundation,single,top,
    scheme,compare,leading,obedient,lies,selected,ticket,pool,onFrame paid bank lamp F J bliss leading obedient⟩

theorem original (axis:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(σ:WilsonOriginalAllOrderCourse.Schedule G):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
    WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R T W ∧
    ∀(cohort:Ultrafilter (ℕ×ℕ)→Prop), (∀(v:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤v.fuse→cohort l)→
      ∀v:Extraction.Order,Elected.{u} R simple cohort v:=by
  obtain ⟨R,T,W,paid,bank,lamp,_⟩:=WilsonOriginalPhysicalFirstEntryOwnerFinance.original.{u} axis simple positive σ
  exact ⟨R,T,W,paid,onRun paid bank lamp⟩

end YM.Integration.WilsonOriginalGeneralRosterElection
end
