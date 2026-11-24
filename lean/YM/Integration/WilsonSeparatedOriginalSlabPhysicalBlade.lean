import YM.Integration.WilsonReportHarvestSlabPhysicalGerm
import YM.Integration.WilsonSeparatedOriginalSlabFolioStamp

/-! The complete physical three-mark field is a genuine single rooted Blade for the original full cabinet.  The retained and amplified programs are combined on the same gauge before the center functional is applied. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabPhysicalBlade
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

open private observed from YM.Integration.WilsonReportHarvestSlabPhysicalGerm

def expense (δ fee:ℝ):ℝ:=(‖(δ:ℂ)‖+‖1-(δ:ℂ)‖)*(4*(1/fee))

theorem bounded {δ fee:ℝ}(d0:0≤δ)(f0:0≤fee):expense δ fee ≤ (1+2*δ)*(4*(1/fee)):=by
  have one:‖(1:ℂ)-(δ:ℂ)‖≤1+δ:=by simpa [Real.norm_of_nonneg d0] using norm_sub_le (1:ℂ) (δ:ℂ)
  apply mul_le_mul_of_nonneg_right _ (by positivity);rw [Complex.norm_real,Real.norm_of_nonneg d0];linarith

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
    (reach:∀i:Fin 3,coverNumber (((C).path.levels.budget (b+1)).B)
      ({o 0,o i}:Support ((C).side (b+1) per)) ≤ peepers (C).path.levels (b+1)) :
    let n:=b+1
    let t:=m+1
    let roster:=Stock.census (Fin 3)
    let J:=Mine.ward o E roster
    let Y:=(C).path.rep N per
    let color:=WilsonAllDateHarvestPhysical.columns o E s q S x a N n
    let real:=gust (C).path N per N (birth (J n) (Y N) color) n (nt.le.trans top)
    let fee:=Many.fee C t n d kLow 3 (Q*((C).S.a a/(C).S.a t))
    0<fee ∧ ∃ x:Three G ((C).side n per),Useful (Y n) x ∧
      (∀W,x.1 W=(baseFold o E roster (real W)).part entire) ∧
      MergeProof.Float.Blade (Y n) (o 0) x.2.1 (profile (Y n).activities x.2.2) 0 (expense δ fee):=by
  intro n t roster J Y color real fee
  obtain ⟨_,board,_,_,H,K,legal,field,reg,hard⟩:=held
  obtain ⟨L,U,lo,hi,_,states⟩:=WilsonReportHarvestSlabBranches.original o E s q R.makes book stock P S x
    roster basis (Nat.le_of_lt_succ nt) na aturn top occ cap one sizes warm degree clear board.fettled
    pos H K legal field reg hard
  have qualified:=WilsonReportHarvestSlabMarker.original R na aturn nt top tiers s S P x o E q
    basis occ cap one sizes warm degree (Nat.zero_lt_succ b) reach
  obtain ⟨money,left,luse,lr,lp⟩:=qualified L lo (states (n+1) n.le_succ nt).2.1
  obtain ⟨_,right,ruse,rr,rp⟩:=qualified U hi (states (n+1) n.le_succ nt).2.2
  let z:ℂ:=δ
  let fresh:=z • right
  let kept:=(1-z) • left
  have hf:=Useful.smul (Y n) right z ruse
  have hk:=Useful.smul (Y n) left (1-z) luse
  have joined:=Useful.join (Y n) (R.makes.wilson.represents N per n (nt.le.trans top)).good hf hk
  refine ⟨money,fresh+kept,joined,?_,?_⟩
  · intro W
    change z*right.1 W+(1-z)*left.1 W=_
    have genuine:real W=WilsonAllDateHarvestAffine.blend (L n W) (U n W) z:=congr_fun (states n le_rfl nt.le).1 W
    rw [rr,lr,genuine]
    have e:=observed o E (L n W) (U n W) z
    linear_combination -e
  · change MergeProof.Float.Blade _ _ (z • right.2.1+(1-z) • left.2.1) (profile _ (z • right.2.2+(1-z) • left.2.2)) 0 _
    have dr:Dominated (z • right.2.2):=hf.normK
    have dl:Dominated ((1-z) • left.2.2):=hk.normK
    rw [MergeProof.Float.prof_add _ dr dl,profile_scale,profile_scale]
    have paid:=(rp.rate z).comp (lp.rate (1-z))
    simpa only [mul_zero,add_zero,expense,add_mul,z] using paid

end YM.Integration.WilsonSeparatedOriginalSlabPhysicalBlade
