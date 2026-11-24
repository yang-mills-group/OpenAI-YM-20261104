import YM.Integration.WilsonReportHarvestSlabPhysicalGerm
import YM.Integration.WilsonSeparatedOriginalSlabBladeModule
import YM.Integration.WilsonSeparatedOriginalSlabPhysicalCredit
import YM.Integration.WilsonSeparatedOriginalSlabRootMarker
import YM.Integration.WilsonSeparatedOriginalSlabMaskBlend

/-! Every marked product has one useful complete Wilson field at the same reporting origin on the full real group. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabRootedCredit
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

open WilsonSeparatedOriginalSlabBladeModule WilsonSeparatedOriginalSlabPhysicalBlade

variable {G:Gauge} (R:Run G)
set_option quotPrecheck false
local notation "C" => R.family

theorem original {b a m N per d kHigh kLow:ℕ} (na:b+1 ≤ a) (aturn:a ≤ m+1) (nt:b+1 < m+1) (top:m+1 ≤ N)
    (book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors) (stock:Storage C R.doors) (tiers:Cater C R.doors)
    {B:ℕ→ℕ→ℝ} (s:Fin 3→ℕ) (S:(i:Fin 3)→Emblems C (s i)) (P:(i:Fin 3)→Sight C (s i) per)
    (x:(i:Fin 3)→Palette C (s i)) (o:Fin 3→Site ((C).side (b+1) per)) (E:Fin 3→Motion)
    (q:ManyStem C o (b+1)→Body) (basis:∀i,Spine R.doors B R.makes (b+1) per (s i) N (P i) (S i))
    (occ:Occupancy o ((C).path.levels.clock.J (b+1))) (cap:∀i:ManyStem C o (b+1),Cap (s i.val.1+2) (q i) 1)
    {Q δ:ℝ} (one:1 ≤ Q) (sizes:∀i,size (x i) ≤ Q) (warm:Warm C (b+1) (d+1) kLow)
    (degree:∀i,s i ≤ d) (clear:Clearance o E s (headings o E q) (Stock.census (Fin 3)) a) (pos:0<δ) (enough:3≤(C).path.levels.clock.J (b+1))
    (held:WilsonReportHarvestReplayPhysical.Retained R na aturn top s S P x o E q (Stock.census (Fin 3)) d kHigh Q δ)
    (reach:∀i:Fin 3,coverNumber (((C).path.levels.budget (b+1)).B)
      ({0,o i}:Support ((C).side (b+1) per)) ≤ peepers (C).path.levels (b+1))
    (mask:(Stock.census (Fin 3)).Mode) :
    let n:=b+1
    let t:=m+1
    let Y:=(C).path.rep N per
    let f:=WilsonSeparatedOriginalCaptureAtOrigin.clinics o E s q S x a N
    let fee:=RG05Readout.Petra.Root.boon C 3 n (peepers (C).path.levels n) (Many.crust C t n d kLow (Q*((C).S.a a/(C).S.a t))/2)
    0<fee ∧ Filed (Y n) 0 (fun W=>RG16.Literal.credit C N per 0
      (fun U=>∏i∈mask.val,f i U) n (nt.le.trans top) W) (WilsonSeparatedOriginalSlabPhysicalBlade.expense δ fee):=by
  intro n t Y f fee
  let roster:=Stock.census (Fin 3)
  let A:=Mine.tree o E
  let J:=Mine.ward o E roster
  let columns:=WilsonAllDateHarvestPhysical.columns o E s q S x a N n
  let real:=gust (C).path N per N (birth (J n) (Y N) columns) n (nt.le.trans top)
  have law:=(R.makes.wilson.represents N per n (nt.le.trans top)).good
  obtain ⟨_,board,_,_,H,K,legal,field,reg,hard⟩:=held
  obtain ⟨L,U,lo,hi,_,states⟩:=WilsonReportHarvestSlabBranches.original o E s q R.makes book stock P S x
    roster basis (Nat.le_of_lt_succ nt) na aturn top occ cap one sizes warm degree clear board.fettled
    pos H K legal field reg hard
  have qualified:=WilsonSeparatedOriginalSlabRootMarker.original R na aturn nt top tiers s S P x o E q
    basis occ cap one sizes warm degree (Nat.zero_lt_succ b) enough reach
  have lchan:=qualified L lo (states (n+1) n.le_succ nt).2.1
  have uchan:=qualified U hi (states (n+1) n.le_succ nt).2.2
  have lp:=lchan.2 mask
  have up:=uchan.2 mask
  let z:ℂ:=δ
  have both:=WilsonSeparatedOriginalSlabBladeModule.add (Y n) 0 law
    (scale (Y n) 0 up z) (scale (Y n) 0 lp (1-z))
  refine ⟨lchan.1,?_⟩
  have eq:(fun W=>RG16.Literal.credit C N per 0 (fun U=>∏i∈mask.val,f i U) n (nt.le.trans top) W)=
      z • (fun W=>(baseFold o E roster (U n W)).part mask)+(1-z) • (fun W=>(baseFold o E roster (L n W)).part mask):=by
    funext W
    have credit:=WilsonSeparatedOriginalSlabPhysicalCredit.original (m:=a) C o E s q S x R.makes (nt.le.trans top) mask W
    refine credit.symm.trans ?_
    change (baseFold o E roster (real W)).part mask=z*(baseFold o E roster (U n W)).part mask+(1-z)*(baseFold o E roster (L n W)).part mask
    have genuine:real W=WilsonAllDateHarvestAffine.blend (L n W) (U n W) z:=congr_fun (states n le_rfl nt.le).1 W
    rw [genuine];exact WilsonSeparatedOriginalSlabMaskBlend.original o E mask (L n W) (U n W) z
  rw [eq,WilsonSeparatedOriginalSlabPhysicalBlade.expense,add_mul,show (4:ℝ)*(1/fee)=4/fee by ring];exact both

end YM.Integration.WilsonSeparatedOriginalSlabRootedCredit
