import YM.Integration.WilsonReportHarvestSlabBranches
import YM.Integration.WilsonReportHarvestSlabMarker
import YM.Integration.WilsonReportHarvestSlabFees
import YM.Integration.WilsonReportHarvestRetainedSlab

/-! The signed difference between the actual cutoff field and the retained
zero-mixed program is one genuine grade-zero coefficient on the same old
Wilson trajectory. The earlier read is the whole original normalized
signed density. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabPhysicalGerm
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

private theorem affine {I J:Type*}[DecidableEq I][DecidableEq J]{A:Census I}{B:Census J}
    (f:Poly A →ₗ[ℂ] Poly B)(L U:Poly A)(z:ℂ)(cell:B.Mode):
    (f (L+z • (U-L))).part cell-(f L).part cell=z*((f U).part cell-(f L).part cell) := by
  have eq:f (L+z • (U-L))=f L+z • (f U-f L):=by rw [map_add,map_smul,map_sub]
  rw [eq]
  change (f L).part cell+z*((f U).part cell-(f L).part cell)-(f L).part cell=_
  ring

private theorem observed {G:Gauge} {C:Family G} {n per:ℕ} (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion)
    (L U:Poly (Mine.ward o E (Stock.census (Fin 3)) n)) (z:ℂ):
    (baseFold o E (Stock.census (Fin 3)) (WilsonAllDateHarvestAffine.blend L U z)).part entire-
      (baseFold o E (Stock.census (Fin 3)) L).part entire=
      z*((baseFold o E (Stock.census (Fin 3)) U).part entire-(baseFold o E (Stock.census (Fin 3)) L).part entire):=by
  let f:Poly (Mine.ward o E (Stock.census (Fin 3)) n) →ₐ[ℂ] Poly (Stock.census (Fin 3)):=
    feed (fun _=>(1:ℂ)) (chamber (Stock.census (Fin 3)) ((Mine.tree o E).labelY n))
  exact affine f.toLinearMap L U z entire

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
    (degree:∀i,s i ≤ d) (clear:Clearance o E s (headings o E q) (Stock.census (Fin 3)) a) (pos:0<δ)
    (held:WilsonReportHarvestReplayPhysical.Retained R na aturn top s S P x o E q (Stock.census (Fin 3)) d kHigh Q δ)
    (eligible:3 ≤ (C).path.levels.clock.J b) (home:((C).path.levels.clock.op b per).ratio.parent (o 0)=0)
    (reach:∀i:Fin 3,coverNumber (((C).path.levels.budget (b+1)).B)
      ({o 0,o i}:Support ((C).side (b+1) per)) ≤ peepers (C).path.levels (b+1)) :
    let n:=b+1
    let t:=m+1
    let roster:=Stock.census (Fin 3)
    let A:=Mine.tree o E
    let J:=Mine.ward o E roster
    let Y:=(C).path.rep N per
    let rows:=imprint R.makes A (headings o E q) (plants (m:=a) s P S x) t top
    let color:=WilsonAllDateHarvestPhysical.columns o E s q S x a N n
    let real:=gust (C).path N per N (birth (J n) (Y N) color) n (nt.le.trans top)
    let gate:=WilsonAllDateHarvestEndpointOpening.opening
      (WilsonMixedTaggedSeparatedBoard.admitted o E roster na aturn) (shadow A s (headings o E q) t)
    let inlet:=fun W=>gate (density (Y t) rows (fun _ _=>0) (fun _ _=>0) W)
    let price:=Many.fee C t n d kLow 3 (Q*((C).S.a a/(C).S.a t))
    let cost:=bling (C).path.levels b * (2*δ*(4*(1/price)))
    ∃ L:∀j,Config G ((C).side j per)→Poly (J j),∃route:Replay A s (le_refl n) t L N,
      L t=inlet ∧
      (∀j (nj:n ≤ j) (jt:j ≤ t) V, ((Y j).eval V)⁻¹ • L j V=
        actualTransport C (N:=N) (fun W=>((Y t).eval W)⁻¹ •
          WilsonReportHarvestEarlierSlab.route route j nj jt (inlet W)) jt V) ∧
      0 < price ∧ ∃X:Coefficient ((C).labels.level 0) ((C).side b per),
        X.Format 0 (C).params (Y b) ∧ X.remBound 0 (Y b) (kappa (C).path b) cost ∧
        ((C).labels.level 0).coeffSize X.x ≤ cost ∧
        ∀u (age:u ≤ b),WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age X=
          pushTo (C).path N per (age.trans b.le_succ)
            (fun W=>(baseFold o E roster (real W)).part entire-(baseFold o E roster (L n W)).part entire)
            1/liftVac (C).path N per u 1 := by
  intro n t roster A J Y rows color real gate inlet price cost
  obtain ⟨_,board,_,_,H,K,legal,field,reg,hard⟩:=held
  obtain ⟨L,U,lo,hi,zero,states⟩:=WilsonReportHarvestSlabBranches.original o E s q R.makes book stock P S x
    roster basis (Nat.le_of_lt_succ nt) na aturn top occ cap one sizes warm degree clear board.fettled
    pos H K legal field reg hard
  have qualified:=WilsonReportHarvestSlabMarker.original R na aturn nt top tiers s S P x o E q
    basis occ cap one sizes warm degree (Nat.zero_lt_succ b) reach
  obtain ⟨money,left,luse,lr,lp⟩:=qualified L lo (states (n+1) n.le_succ nt).2.1
  obtain ⟨_,right,ruse,rr,rp⟩:=qualified U hi (states (n+1) n.le_succ nt).2.2
  have budget : 0 ≤ 4*(1/price):=mul_nonneg (by norm_num) (one_div_pos.mpr money).le
  obtain ⟨X,fmt,rem,size,_,read⟩:=WilsonReportHarvestSlabSigned.original R tiers
    (b.lt_succ_self.trans_le (nt.le.trans top)) eligible home right left ruse luse budget pos.le rp lp
  have init:L t=inlet:=zero
  refine ⟨L,lo,init,?_,money,X,fmt,rem,size,fun u age=>?_⟩
  · intro j nj jt V
    rw [←init]
    exact WilsonReportHarvestEarlierSlab.normalized lo R.makes top (states t (na.trans aturn) le_rfl).2.1.cleared nj jt V
  · rw [read u age]
    have exactField:(fun W=>(δ:ℂ)*(right.1 W-left.1 W))=fun W=>
        (baseFold o E roster (real W)).part entire-(baseFold o E roster (L n W)).part entire:=by
      funext W
      have genuine:real W=WilsonAllDateHarvestAffine.blend (L n W) (U n W) (δ:ℂ):=
        congr_fun (states n le_rfl nt.le).1 W
      rw [rr,lr,genuine,observed]
    rw [exactField]

end YM.Integration.WilsonReportHarvestSlabPhysicalGerm
