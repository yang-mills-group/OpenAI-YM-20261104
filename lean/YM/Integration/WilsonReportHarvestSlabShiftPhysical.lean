import YM.Integration.WilsonReportHarvestSlabPhysicalGerm
import YM.Integration.WilsonReportHarvestSlabBranches
import YM.Integration.WilsonReportHarvestSlabShiftMarker
import YM.Integration.WilsonReportHarvestSlabFees
import YM.Integration.WilsonReportHarvestRetainedSlab

/-! The signed difference between the actual cutoff field and the retained
zero-mixed program is one genuine grade-zero coefficient on the same old
Wilson trajectory. The earlier read is the whole original normalized
signed density. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabShiftPhysical
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

open private affine from YM.Integration.WilsonReportHarvestSlabPhysicalGerm

private theorem unshifted {G:Gauge} {C:Family G} {n per:ℕ} (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion)
    (L U:Poly (Mine.ward o E (Stock.census (Fin 3)) n)) (z:ℂ)(cell:(Stock.census (Fin 3)).Mode):
    (baseFold o E (Stock.census (Fin 3)) (WilsonAllDateHarvestAffine.blend L U z)).part cell-
      (baseFold o E (Stock.census (Fin 3)) L).part cell=
      z*((baseFold o E (Stock.census (Fin 3)) U).part cell-(baseFold o E (Stock.census (Fin 3)) L).part cell):=by
  let f:Poly (Mine.ward o E (Stock.census (Fin 3)) n) →ₐ[ℂ] Poly (Stock.census (Fin 3)):=
    feed (fun _=>(1:ℂ)) (chamber (Stock.census (Fin 3)) ((Mine.tree o E).labelY n))
  exact affine f.toLinearMap L U z cell



private theorem scored (L U X:Poly (Stock.census (Fin 3))) (z:ℂ) (v:Fin 3→ℂ)
    (same:∀cell,X.part cell-L.part cell=z*(U.part cell-L.part cell)) (cell:(Stock.census (Fin 3)).Mode):
    (WilsonReportHarvestSlabShiftLabels.translated v X).part cell-
      (WilsonReportHarvestSlabShiftLabels.translated v L).part cell=z*((WilsonReportHarvestSlabShiftLabels.translated v U).part cell-
      (WilsonReportHarvestSlabShiftLabels.translated v L).part cell):=by
  have full:X=L+z • (U-L):=by
    ext c
    change X.part c=L.part c+z*(U.part c-L.part c)
    linear_combination same c
  let f:=LinearMap.mulLeft ℂ (Poly.pass (Mach (Stock.census (Fin 3)) v))
  change (f X).part cell-(f L).part cell=z*((f U).part cell-(f L).part cell)
  rw [full,map_add,map_smul,map_sub]
  change (f L).part cell+z*((f U).part cell-(f L).part cell)-(f L).part cell=_
  ring

private theorem shifted {G:Gauge} {C:Family G} {n per:ℕ} (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion)
    (L U:Poly (Mine.ward o E (Stock.census (Fin 3)) n)) (z:ℂ) (v:Fin 3→ℂ) (cell:(Stock.census (Fin 3)).Mode):
    (WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E (Stock.census (Fin 3))
      (WilsonAllDateHarvestAffine.blend L U z))).part cell-
      (WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E (Stock.census (Fin 3)) L)).part cell=
      z*((WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E (Stock.census (Fin 3)) U)).part cell-
      (WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E (Stock.census (Fin 3)) L)).part cell):=by
  exact scored _ _ _ z v (fun c=>unshifted o E L U z c) cell

private theorem plain (A:Poly (Stock.census (Fin 3))):
    WilsonReportHarvestSlabShiftLabels.translated 0 A=A:=by
  unfold WilsonReportHarvestSlabShiftLabels.translated Mach
  simp only [Pi.zero_apply,Poly.send_zero,Finset.sum_const_zero,Push.GridApprox.Nil.pass_zero,one_mul]

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
      Integrable (fun V=>baseFold o E roster (L n V)) (prior G ((C).side n per)) ∧
      (∀V,(baseFold o E roster (real V)).part roster.quiet=(baseFold o E roster (L n V)).part roster.quiet) ∧
      (∀i V,(baseFold o E roster (real V)).part (roster.fire i)=(baseFold o E roster (L n V)).part (roster.fire i)) ∧
      ∀v:Fin 3→ℂ,(∀i,‖v i‖≤1) → 0 < price ∧ ∃X:Coefficient ((C).labels.level 0) ((C).side b per),
        X.Format 0 (C).params (Y b) ∧ X.remBound 0 (Y b) (kappa (C).path b) cost ∧
        ((C).labels.level 0).coeffSize X.x ≤ cost ∧
        ∀u (age:u ≤ b),WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age X=
          pushTo (C).path N per (age.trans b.le_succ)
            (fun W=>(WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E roster (real W))).part entire-
              (WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E roster (L n W))).part entire)
            1/liftVac (C).path N per u 1 := by
  intro n t roster A J Y rows color real gate inlet price cost
  obtain ⟨_,board,_,_,H,K,legal,field,reg,hard⟩:=held
  obtain ⟨L,U,lo,hi,zero,states⟩:=WilsonReportHarvestSlabBranches.original o E s q R.makes book stock P S x
    roster basis (Nat.le_of_lt_succ nt) na aturn top occ cap one sizes warm degree clear board.fettled
    pos H K legal field reg hard
  have qualified:=WilsonReportHarvestSlabShiftMarker.original R na aturn nt top tiers s S P x o E q
    basis occ cap one sizes warm degree (Nat.zero_lt_succ b) reach
  obtain ⟨expose,left0,left1,buyL⟩:=qualified L lo (states (n+1) n.le_succ nt).2.1
  obtain ⟨_,right0,right1,buyU⟩:=qualified U hi (states (n+1) n.le_succ nt).2.2
  have init:L t=inlet:=zero
  have genuine (V):real V=WilsonAllDateHarvestAffine.blend (L n V) (U n V) (δ:ℂ):=
    congr_fun (states n le_rfl nt.le).1 V
  have same (V) (cell:roster.Mode) (same:(baseFold o E roster (U n V)).part cell=(baseFold o E roster (L n V)).part cell):
      (baseFold o E roster (real V)).part cell=(baseFold o E roster (L n V)).part cell:=by
    have eq:=shifted o E (L n V) (U n V) (δ:ℂ) 0 cell
    simp only [plain,←genuine V] at eq
    exact sub_eq_zero.mp (eq.trans (mul_eq_zero_of_right _ (sub_eq_zero.mpr same)))
  refine ⟨L,lo,init,?_,expose,fun V=>same V _ ((right0 V).trans (left0 V).symm),
    fun i V=>same V _ ((right1 i V).trans (left1 i V).symm),?_⟩
  · intro j nj jt V
    rw [←init]
    exact WilsonReportHarvestEarlierSlab.normalized lo R.makes top (states t (na.trans aturn) le_rfl).2.1.cleared nj jt V
  · intro v bounded
    obtain ⟨money,left,luse,lr,lp⟩:=buyL v bounded
    obtain ⟨_,right,ruse,rr,rp⟩:=buyU v bounded
    have budget:0 ≤ 4*(1/price):=le_of_lt (mul_pos (by norm_num) (one_div_pos.mpr money))
    obtain ⟨X,fmt,rem,size,_,read⟩:=WilsonReportHarvestSlabSigned.original R tiers
      (b.lt_succ_self.trans_le (nt.le.trans top)) eligible home right left ruse luse budget pos.le rp lp
    refine ⟨money,X,fmt,rem,size,fun u age=>?_⟩
    rw [read u age]
    have exactField:(fun W=>(δ:ℂ)*(right.1 W-left.1 W))=fun W=>
        (WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E roster (real W))).part entire-
        (WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E roster (L n W))).part entire:=by
      funext W
      rw [rr,lr,genuine W,shifted]
    rw [exactField]

end YM.Integration.WilsonReportHarvestSlabShiftPhysical
