import YM.Integration.WilsonSeparatedOriginalSlabChildCell
import YM.Integration.WilsonSeparatedOriginalSlabPhysical
import YM.Integration.WilsonSeparatedOriginalSlabChildSupport
import YM.Integration.WilsonSeparatedOriginalSlabChildCapture

/-! The full nonseparable physical assay has one finite priced signed folio per original parent. Its submitted grades are real transported old-field outputs in every translated incoming cell. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildPortfolio
open Function Finset Set Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open RG05Readout.Nuclear RG05Readout.Pulse Push.GridApprox
open WilsonSeparatedOriginalSlabPosting WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabFolio
open WilsonSeparatedOriginalSlabChildSites
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){b m t N per:ℕ}(nm:b+1 ≤ m)(mt:m ≤ t)(nt:b+1 < t)(tN:t ≤ N)
variable (s:Fin 3 → ℕ)(S:(i:Fin 3) → Emblems R.family (s i))(P:(i:Fin 3) → Sight R.family (s i) per)(x:(i:Fin 3) → Palette R.family (s i))
local notation "C"=>R.family
local notation "n"=>b+1
local notation "Sites"=>Site ((C).side (b+1) per)
local notation "Origins"=>Fin 3 → Sites
local notation "fine"=>fun i:Fin 3=>Launch (m:=m) s S x i N
local notation "top"=>nt.le.trans tN
local notation "A"=>R.family.S.oneStep b per
local notation "meter"=>WilsonSeparatedOriginalSlabChildCell.sensor R (per:=per) s fine top
local notation "price"=>1+WilsonPositionSeparatedProfileStableReturn.price

def Booked (hb:(C).ref 0 ≤ b)(o:Origins)(f:Fin 3 → Body)(w:Sites → ℂ):Prop:=
  ∀c,∃F:Dates R b → ℂ,Posted R nm mt nt tN s S P x (site A o c) f F ∧ w c=F ⟨b,hb,le_rfl⟩

theorem marked (hb:(C).ref 0 ≤ b)(book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors)
    (o:Origins)(f:Fin 3 → Body){δ:ℝ}(taken:∀c,WilsonReportHarvestSlabShiftReceipt.Captured R nm mt nt tN s S P x (site A o c) (fun _=>(1,false)) (fun z=>f z.val.1) δ):
    ∃F:Sites → ℂ,WilsonSeparatedOriginalSlabWholeProfile.settled R meter o (Booked R nm mt nt tN s S P x hb o) ((price)*δ) f F:=by
  choose table cash using fun c:Sites=>WilsonSeparatedOriginalSlabPosting.issued R nm mt nt tN s S P x (site A o c) book f (taken c)
  let d:Dates R b:=⟨b,hb,le_rfl⟩
  refine ⟨fun c=>table c d,fun c=>⟨table c,(cash c).1,rfl⟩,?_⟩
  intro c;exact (cash c).2 d

def Readout (hb:(C).ref 0 ≤ b)(Ψ:Wave (Fin 3))(rank:ℕ)(r η X cap:ℝ)(g:Body)(ε bill:ℝ):Prop:=
  let bought:=fun o=>WilsonSeparatedOriginalSlabWholeProfile.settled R meter o (Booked R nm mt nt tN s S P x hb o) ε
  let Q:=earn s C n rank η r*X
  let A₀:=Pulse.area («C»:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊
  ∃L:(o:Origins) → List (Entry s (allowed R s o r η) (bought o)),
    (∀o,o∉A₀ → L o=[]) ∧ (∀o∈A₀,((L o).map Entry.rent).sum ≤ Q) ∧ ∀c:Sites,
      ‖WilsonSeparatedOriginalSlabWholeProfile.whole R s meter r Ψ m g c-premiums C s m n r*∑o:Origins,received g (L o) c‖ ≤ bill

theorem purchased (hb:(C).ref 0 ≤ b)(book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors)
    {δ r η X cap:ℝ}(δp:0 ≤ δ)(rp:0<r)(room:r ≤ (C).S.a n)(ep:0<η)(small:η ≤ 1)
    (Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)(cp:0 ≤ cap)
    (shape:∀y∈tsupport Ψ.val,∀i:Fin 3,‖y i‖ ≤ cap)(g:Body)
    (take:∀o∈Pulse.area («C»:=R.family) (p:=per) (b:=n) ⌈cap+2⌉₊,∀c,∀f:Fin 3 → Body,
      (∀i,Tall (f i) (s i+2) 1 1) → buy C n per o (r*η/2) f →
      WilsonReportHarvestSlabShiftReceipt.Captured R nm mt nt tN s S P x (site A o c) (fun _=>(1,false)) (fun z=>f z.val.1) δ):
    Readout R nm mt nt tN s S P x hb Ψ rank r η X cap g ((price)*δ)
      (WilsonSeparatedOriginalProfileTariff.budget C s n rank r η X cap g*((price)*δ)):=by
  have nonneg:0 ≤ WilsonPositionSeparatedProfileStableReturn.price:=div_nonneg WilsonPositionSeparatedProfileStableStep.shrink_pos.le (sub_pos.mpr WilsonPositionSeparatedProfileStableStep.shrink_lt).le
  have pos:0 ≤ (price)*δ:=mul_nonneg (by linarith) δp
  obtain ⟨L,empty,cost,paid⟩:=WilsonSeparatedOriginalSlabWholeProfile.original R s top meter
    (Booked R nm mt nt tN s S P x hb) pos rp room ep small Ψ rank grade scatter xp sizeX
    (fun o c=>WilsonSeparatedOriginalSlabWave.same R s fine (site A o c) top top 1)
    (fun o gone c z hz=>WilsonSeparatedOriginalSlabChildSupport.raw R s fine top A o c rp Ψ shape _ gone
      (WilsonSeparatedOriginalReplicaSupport.radius C n cp room) z hz top 1)
    (fun o live f admit=>marked R nm mt nt tN s S P x hb book o f (fun c=>take o live c f admit.2 admit.1))
  exact ⟨L,empty,cost,fun c=>(paid m g c).trans (WilsonSeparatedOriginalProfileTariff.full C s m n rank rp η X cap g pos)⟩

end YM.Integration.WilsonSeparatedOriginalSlabChildPortfolio
