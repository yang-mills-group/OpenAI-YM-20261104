import YM.Integration.WilsonOriginalGeneralRosterHomeRegistered
import YM.Integration.WilsonOriginalGeneralRosterLowerInvoice

/-! One original funded campaign issues both the paid upper roster
and the actual lower archive. The finite loss vector precedes every
thermal order. Every lower receipt uses that row's real test and the
complete union's reserve, cap, and pole. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterOriginalCourse

open Climb Lattice Filter Function Set Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open RG RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedMixedMasterSchool (field)
open WilsonOriginalGeneralRosterUnion (Row)
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open XSpace
open WilsonOriginalOpticalSchedule (prepared)
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{simple:G.Simple}{axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {T₀:Campaign R}{W₀:Campaign.Pillars R T₀}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R T₀ W₀)
    {v:Extraction.Order}{S:Table R.family.book}{F:Final R.family v S}
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop}{J:ℝ→PhysMS.tower S}

def Household (bliss:Bliss F l z H)(lead:Leading F J)(obeys:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (below:(l:Filter (ℕ×ℕ))≤v.fuse)(lamp:WilsonReportLampForecast.Ready R.family.path.levels):Prop:=
  ∀(n:ℕ)(Z:WilsonPrescription G)(D:ℕ),∃t≥D+3,∃T:ℕ,∃δ:ℝ,0<δ ∧
    ∃books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
    ∃_priced:∀s,WilsonMovingForkWindowBooks.Priced F (books s),
    ∀(h:ℕ)(d:Fin (n+1)→Fin (D+1))(y:∀i,(Spin.comparator R.family.book).Field (d i).val)
      (x:∀i,RG17.Free R.family (d i).val),
    let nominated:=field F J Z D T d y x books
    let income:=WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid
    ∃sale:WilsonOriginalGeneralRosterHomeReturn.Register F books h t d nominated,
    ∃college:∀(scheme:Initialize G)(a k u e:ℕ)(tag:Fin (a+1)→Fin (n+1))(cap:Fin (a+1)→ℕ)
      (fit:∀i,(d (tag i)).val<cap i)(kind:Fin (a+1)→Bool)(own:∀i,Rails (d (tag i)).val k u e),
      WilsonOriginalGeneralRosterHomeBank.Booked F books h t d nominated scheme tag cap fit kind own,
    (∀(scheme:Initialize G)(a k u e:ℕ)(tag:Fin (a+1)→Fin (n+1))(cap:Fin (a+1)→ℕ)(fit:∀i,(d (tag i)).val<cap i)
      (kind:Fin (a+1)→Bool)(own:∀i,Rails (d (tag i)).val k u e)(index:ℕ)(positive:0 < index)
      (ratio:Z.run.ratio=(3:ℕ)^index)(stage before infrared:ℕ),
      type_of% (WilsonOriginalGeneralRosterHomeEscorted.original F books paid nominated Z scheme tag cap fit kind own
        (college scheme a k u e tag cap fit kind own) bliss income.2.1 lamp positive ratio stage before infrared)) ∧
    (∀(ax:Fin (n+1)→Axis)(E:Fin (n+1)→Set (Points 2))(compact:∀i,IsCompact (E i))(sep:∀i,E i⊆conf 2),
      type_of% (WilsonOriginalGeneralRosterHomeSelf.original F J Z simple bliss lead obeys below books d x ax E compact sep h)) ∧
    ∀(B:Type)[Fintype B](main:Row (Fin (n+1)))(pair:Fin main.size→Test 2)(p:Fin main.size→ℕ)
      (outside:B→Row (Fin (n+1)))(home:B→Option (Fin (n+1))),
      type_of% (WilsonOriginalGeneralRosterHomeMenu.original F books nominated sale main pair p outside home)

theorem onFrame (bliss:Bliss F l z H)(lead:Leading F J)(obeys:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (below:(l:Filter (ℕ×ℕ))≤v.fuse)(lamp:WilsonReportLampForecast.Ready R.family.path.levels)
    (enrolled:WilsonOriginalGeneralRosterHomeRegistered.Programme paid bliss lead obeys below):
    Household paid bliss lead obeys below lamp:=by
  intro n Z D
  obtain ⟨t,dt,T,δ,small,books,priced,finance⟩:=enrolled n Z D
  refine ⟨t,dt,T,δ,small,books,priced,?_⟩
  intro h d y x nominated income
  obtain ⟨sale,bank,_source,self,_dates,menu⟩:=finance h d y x
  exact ⟨sale,bank,fun scheme a k u e tag cap fit kind own _ positive ratio stage before infrared=>
    WilsonOriginalGeneralRosterHomeEscorted.original F books paid nominated Z scheme tag cap fit kind own
      (bank scheme a k u e tag cap fit kind own) bliss income.2.1 lamp positive ratio stage before infrared,self,menu⟩

def Lower (under:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared σ) R T₀ W₀)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(lamp:WilsonReportLampForecast.Ready R.family.path.levels):Prop:=
  ∀(I B U:Type)[Fintype I][Fintype B][Fintype U](D term h:ℕ)(d:I→Fin (D+1))(M:I→ℝ)(E:I→ℕ)
    (main:Row I)(pair:Fin main.size→Test 2)(precision:Fin main.size→ℕ)(outside:B→Row I)
    (w:Unit⊕(Fin main.size⊕B))(wanted:ℕ),
    type_of% (WilsonOriginalGeneralRosterLowerInvoice.original (U:=U) under paths lamp term h d M E main pair precision outside w wanted)

theorem original (axis:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(σ:WilsonOriginalAllOrderCourse.Schedule G):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),∃p:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared σ) R T W,
    ∃lamp:WilsonReportLampForecast.Ready R.family.path.levels,∃paths:FundedOriginalVacuumPaths.prices R.kit,
    Lower p paths lamp ∧
    ∀(cohort:Ultrafilter (ℕ×ℕ)→Prop),(∀(v:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤v.fuse→cohort l)→
      ∀v:Extraction.Order,∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (L:EveryPhase.Almanac F)(Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(H:(Bel R.family.book).Hierarchy),
      ∃z:Trace.Terrace.Arch R.family,∃l:Ultrafilter (ℕ×ℕ),∃J:ℝ→PhysMS.tower S,
      ∃chosen:WilsonViewerElectedHierarchy.Selected.{u} F L Q J H z l simple cohort,
        Household p chosen.bliss chosen.leading chosen.obeys chosen.original lamp:=by
  obtain ⟨R,T,W,p,bank,lamp,paths⟩:=WilsonOriginalPhysicalFirstEntryOwnerFinance.original.{u} axis simple positive (prepared σ)
  refine ⟨R,T,W,p,lamp,paths,?_,?_⟩
  · intro I B U _ _ _ D term h d M E main pair precision outside w wanted
    exact WilsonOriginalGeneralRosterLowerInvoice.original (U:=U) p paths lamp term h d M E main pair precision outside w wanted
  intro cohort eligible v
  obtain ⟨w,S,F,L,Q,H,z,l,J,chosen,physical⟩:=WilsonOriginalGeneralRosterHomePhysical.onRun p bank lamp cohort eligible v
  exact ⟨w,S,F,L,Q,H,z,l,J,chosen,onFrame p chosen.bliss chosen.leading chosen.obeys chosen.original lamp
    (WilsonOriginalGeneralRosterHomeRegistered.onFrame p chosen.bliss chosen.leading chosen.obeys chosen.original physical)⟩

end YM.Integration.WilsonOriginalGeneralRosterOriginalCourse
end
