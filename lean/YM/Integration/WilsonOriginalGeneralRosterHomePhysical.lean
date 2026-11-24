import YM.Integration.WilsonOriginalGeneralRosterElection
import YM.Integration.WilsonOriginalGeneralRosterHomeReturn
import YM.Integration.WilsonViewerElectedHierarchy

/-! A single original physical election supports the unrestricted paired-flat
response at independent test radii for every finite family of subsequent experiments of mixed arity, on one shared set of files and matrices. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterHomePhysical
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open RG RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedMixedMasterSchool (field)
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{simple:G.Simple}

def Experiments {v:Extraction.Order}{S:Table R.family.book}(F:Final R.family v S)
    (l:Ultrafilter (ℕ×ℕ))(H:(Bel R.family.book).Hierarchy)(z:Trace.Terrace.Arch R.family)
    (J:ℝ→PhysMS.tower S):Prop:=
  ∀(I:Type)[Fintype I][Nonempty I](Z:WilsonPrescription G)(D:ℕ),
    ∃t≥D+3,∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
    (∀s,WilsonMovingForkWindowBooks.Priced F (books s)) ∧ ∀(h:ℕ)(d:I→Fin (D+1))
    (y:∀i,(Spin.comparator R.family.book).Field (d i).val)(x:∀i,RG17.Free R.family (d i).val),
    WilsonOriginalGeneralRosterHomeReturn.Register F books h t d (field F J Z D T d y x books)

theorem onFrame {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {T:Campaign R}{W:Campaign.Pillars R T}(paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R T W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels)
    (lamp:WilsonReportLampForecast.Ready R.family.path.levels)
    {v:Extraction.Order}{S:Table R.family.book}(F:Final R.family v S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    (J:ℝ→PhysMS.tower S)(bliss:Bliss F l z H)(lead:Leading F J)
    (obedient:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)(fac:Facilities R.family v S):Experiments F l H z J:=by
  intro I _ _ Z D
  obtain ⟨t,td,T,δ,dp,books,amount,grant⟩:=WilsonMeasuredPublicEntrancePublicFaculty.onFrame
    paid F J bliss lead obedient I Z D
  refine ⟨t,td,T,δ,dp,books,amount,?_⟩
  intro h d y x
  exact WilsonOriginalGeneralRosterHomeReturn.original F books _ fac bliss
    (WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid).2.1
    (WilsonOriginalGeneralRosterHomeUnion.original F books _ paid bank lamp bliss (grant h d y x))

def Elected (R:Run G)(simple:G.Simple)(cohort:Ultrafilter (ℕ×ℕ)→Prop)(v:Extraction.Order):Prop:=
  ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
    (L:EveryPhase.Almanac F)(Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:(Bel R.family.book).Hierarchy)(z:Trace.Terrace.Arch R.family)(l:Ultrafilter (ℕ×ℕ))(J:ℝ→PhysMS.tower S),
    WilsonViewerElectedHierarchy.Selected.{u} F L Q J H z l simple cohort ∧ Experiments F l H z J

theorem onRun {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {T:Campaign R}{W:Campaign.Pillars R T}(paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R T W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels)
    (lamp:WilsonReportLampForecast.Ready R.family.path.levels)(cohort:Ultrafilter (ℕ×ℕ)→Prop)
    (select:∀(v:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤v.fuse→cohort l)(v:Extraction.Order):
    Elected.{u} R simple cohort v:=by
  obtain ⟨w,S,F,L,Q,H,z,l,bliss,P,P',J,φ,a,d,e,completed,result,exclusion,fac,foundation,single,top,
    scheme,compare,leading,obedient,lies,selected,ticket,_,_⟩:=
    WilsonOriginalGeneralRosterElection.onRun paid bank lamp cohort select v
  have chosen:WilsonViewerElectedHierarchy.Selected.{u} F L Q J H z l simple cohort:=
    ⟨completed,result,exclusion,fac,foundation,single,bliss,lies,selected,ticket,leading,obedient,
     ⟨P,P',φ,a,d,e,top,scheme,compare⟩⟩
  exact ⟨w,S,F,L,Q,H,z,l,J,chosen,onFrame paid bank lamp F J bliss leading obedient fac⟩

theorem original (axis:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(σ:WilsonOriginalAllOrderCourse.Schedule G):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
    WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R T W ∧
    ∀(cohort:Ultrafilter (ℕ×ℕ)→Prop), (∀(v:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤v.fuse→cohort l)→
      ∀v:Extraction.Order,Elected.{u} R simple cohort v:=by
  obtain ⟨R,T,W,paid,bank,lamp,_⟩:=WilsonOriginalPhysicalFirstEntryOwnerFinance.original.{u} axis simple positive σ
  exact ⟨R,T,W,paid,onRun paid bank lamp⟩

end YM.Integration.WilsonOriginalGeneralRosterHomePhysical
end
