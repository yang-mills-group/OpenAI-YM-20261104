import YM.Integration.WilsonSeparatedOriginalSlabPosting
import YM.Integration.WilsonSeparatedOriginalSlabAtlas

/-! A jointly deposited finite grade-zero reading for every original parent in the support of one arbitrary separated smooth wave. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabPhysical
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extraction RG05Readout
open RG05Readout.Native RG05Readout.Pulse RG05Readout.Address RG05Readout.Nuclear PhysicalNext.Repeat.Legato RG05Readout.Many
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabPosting WilsonSeparatedOriginalSlabFolio
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){b m t N per:ℕ}(nm:b+1 ≤ m)(mt:m ≤ t)(nt:b+1 < t)(tN:t ≤ N)
variable (s:Fin 3 → ℕ)(S:(i:Fin 3) → Emblems R.family (s i))(P:(i:Fin 3) → Sight R.family (s i) per)(x:(i:Fin 3) → Palette R.family (s i))
local notation "C"=>R.family
local notation "n"=>b+1
local notation "Origins"=>Fin 3 → Site (R.family.side (b+1) per)
local notation "Fine"=>fun i:Fin 3=>Launch (m:=m) s S x i N
local notation "top"=>nt.le.trans tN
local notation "age"=>fun a:Dates R b=>a.val
local notation "opened"=>fun a:Dates R b=>(Nat.succ_le_succ a.2.2).trans (nt.le.trans tN)
local notation "held"=>fun a:Dates R b=>(1:Config G (R.family.side a.val per))
local notation "λ₀"=>1+WilsonPositionSeparatedProfileStableReturn.price

def Readout (Ψ:Wave (Fin 3))(rank:ℕ)(r η X cap:ℝ)(g:Body)(atomPrice bill:ℝ):Prop:=
  let sale:=fun o=>settled R s Fine o top age opened held (Posted R nm mt nt tN s S P x o) atomPrice
  let quota:=earn s C n rank η r*X
  let area:=Pulse.area («C»:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊
  ∃L:(o:Origins) → List (Entry s (allowed R s o r η) (sale o)),
    (∀o,o∉area → L o=[]) ∧ (∀o∈area,((L o).map Entry.rent).sum ≤ quota) ∧ ∀a:Dates R b,
      ‖WilsonSeparatedOriginalSlabAtlas.whole R s Fine top age opened held r Ψ m g a-
        premiums C s m n r*∑o:Origins,received g (L o) a‖ ≤ bill

theorem purchased (book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors)
    {ε r η X cap:ℝ}(ep:0 ≤ ε)(rp:0<r)(room:r ≤ (C).S.a n)(sep:0<η)(small:η ≤ 1)
    (Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)(cp:0 ≤ cap)
    (shape:∀y∈tsupport Ψ.val,∀i:Fin 3,‖y i‖ ≤ cap)(g:Body)
    (bought:∀o∈Pulse.area («C»:=R.family) (p:=per) (b:=n) ⌈cap+2⌉₊,∀f:Fin 3 → Body,
      (∀i,Tall (f i) (s i+2) 1 1) → buy C n per o (r*η/2) f →
      WilsonReportHarvestSlabShiftReceipt.Captured R nm mt nt tN s S P x o (fun _=>(1,false)) (fun z=>f z.val.1) ε):
    Readout R nm mt nt tN s S P x Ψ rank r η X cap g ((λ₀)*ε)
      (WilsonSeparatedOriginalProfileTariff.budget C s n rank r η X cap g*((λ₀)*ε)):=by
  let old:=WilsonPositionSeparatedProfileStableReturn.price
  have price:0 ≤ old:=div_nonneg WilsonPositionSeparatedProfileStableStep.shrink_pos.le (sub_pos.mpr WilsonPositionSeparatedProfileStableStep.shrink_lt).le
  have pos:0 ≤ (λ₀)*ε:=mul_nonneg (show 0 ≤ 1+old by linarith) ep
  obtain ⟨L,empty,capacity,paid⟩:=WilsonSeparatedOriginalSlabAtlas.original R s Fine top age opened held
    (fun o=>Posted R nm mt nt tN s S P x o) pos rp room sep small Ψ rank grade scatter xp sizeX cp shape
    (fun o live f admit=>WilsonSeparatedOriginalSlabPosting.issued R nm mt nt tN s S P x o book f (bought o live f admit.2 admit.1))
  refine ⟨L,empty,capacity,?_⟩
  intro a
  exact (paid m g a).trans (WilsonSeparatedOriginalProfileTariff.full C s m n rank rp η X cap g pos)

end YM.Integration.WilsonSeparatedOriginalSlabPhysical
