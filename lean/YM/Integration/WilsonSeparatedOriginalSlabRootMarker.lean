import YM.Integration.WilsonSeparatedOriginalSlabRootedAlcove
import YM.Integration.WilsonSeparatedOriginalSlabMaskRadius
import YM.Integration.WilsonReportHarvestSlabResident

/-! Issue one original mark per selected mask at a single physical origin for every graded parent, holding the entire old gauge field fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabRootMarker
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open WilsonSeparatedOriginalSlabBladeModule RG05Readout.Petra Ribbons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G)
set_option quotPrecheck false
local notation "C" => R.family

theorem original {n a t N per d kLow:ℕ} (na:n≤a) (aturn:a≤t) (nt:n<t) (tN:t≤N)
    (tiers:Cater C R.doors) {B:ℕ→ℕ→ℝ}
    (s:Fin 3→ℕ) (S:(i:Fin 3)→Emblems C (s i)) (P:(i:Fin 3)→Sight C (s i) per)
    (x:(i:Fin 3)→Palette C (s i)) (o:Fin 3→Site ((C).side n per)) (E:Fin 3→Motion)
    (q:ManyStem C o n→Body)
    (basis:∀i,Spine R.doors B R.makes n per (s i) N (P i) (S i))
    (occ:Occupancy o ((C).path.levels.clock.J n)) (cap:∀i:ManyStem C o n,Cap (s i.val.1+2) (q i) 1)
    {Q:ℝ} (one:1≤Q) (sizes:∀i,size (x i)≤Q) (warm:Warm C n (d+1) kLow)
    (degree:∀i,s i≤d) (hn:0<n) (enough:3≤(C).path.levels.clock.J n)
    (reach:∀v:Fin 3,coverNumber (((C).path.levels.budget n).B)
      ({0,o v}:Support ((C).side n per)) ≤ Ribbons.peepers (C).path.levels n) :
    let roster:=Stock.census (Fin 3)
    let A:=Mine.tree o E
    let I:=headings o E q
    let src:=plants (m:=a) s P S x
    let Y:=(C).path.rep N per
    let cash:=Q*((C).S.a a/(C).S.a t)
    let w:=RG05Readout.Many.envelope C t (d+1) kLow cash
    let price:=Root.boon C 3 n (Ribbons.peepers (C).path.levels n) (Many.crust C t n d kLow cash/2)
    ∀ (L:∀i,Config G ((C).side i per)→Poly (Mine.ward o E roster i)),
      Replay A s (le_refl n) t L N →
      MenuBoard (Y (n+1)) (imprint R.makes A I src (n+1) (nt.trans_le tN)) (L (n+1))
        (A.supportX (n+1)) (fun _=>w (n+1))
        (if n+1=t then ((C).path.levels.budget (n+1)).supportExponent-4
         else ((C).path.levels.budget (n+1)).supportExponent) 1 →
      0<price ∧ ∀mask:roster.Mode, Filed (Y n) 0 (fun U=>(baseFold o E roster (L n U)).part mask) (4/price):=by
  intro roster A I src Y cash w price L row next
  let raised:=WilsonAllDateHarvestRebook.raised s S x a t
  have names:plants (m:=t) s P S raised=plants (m:=a) s P S x:=
    WilsonAllDateHarvestRebook.singleton s S x P a t
  dsimp only [src] at next
  rw [←names] at next
  have costs (v:Fin 3):size (raised v)≤cash:=WilsonAllDateHarvestRebook.sizeAt (basis v) na aturn tN (sizes v)
  have liveCash:0<cash:=mul_pos (zero_lt_one.trans_le one) (div_pos ((C).S.a_pos _) ((C).S.a_pos _))
  obtain ⟨base,prepared⟩:=headlines (N:=N) o E q
  have baseCap:∀v:ManyStem C o n,Cap (s ((A).labelY n v)+2) (I n v) 1:=by
    change ∀v:ManyStem C o n,Cap (s v.val.1+2) (headings o E q n v) 1
    rw [base]
    exact cap
  obtain ⟨positive,_,_,furls,invoice⟩:=WilsonReportHarvestSlabFold.original
    o E s (headings o E q) R.makes tiers P S raised basis nt tN occ prepared baseCap
      costs liveCash warm degree next row
  rw [names] at invoice
  let shell:=Ribbons.peepers (C).path.levels n
  have sp:1≤ shell:=by unfold shell Ribbons.peepers;exact Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) _)
  let σ:=Many.crust C t n d kLow cash
  have sealed(v:Fin 3→ℂ)(hv:∀i,‖v i‖≤1):0<price ∧ Filed (Y n) 0
      (fun U=>(WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E roster (L n U))).part WilsonReportHarvestSlabLabels.entire) (4/price):=by
    have bound:∀i,σ*‖v i‖ ≤1/2:=fun i=>(mul_le_of_le_one_right positive.le (hv i)).trans (min_le_left _ _)
    have shifted:=invoice.spiced v bound (fun _=>positive.le)
    have thin:=WilsonSeparatedOriginalSlabMaskRadius.thin (fun _=>positive.le) shifted
    have halved:((1/2:ℝ)+1/2)/2=1/2:=by norm_num
    rw [halved] at thin
    exact WilsonSeparatedOriginalSlabRootedAlcove.original («C»:=R.family) (D:=R.doors) (N:=N) (n:=n) (per:=per)
      (o:=o) (F:=spice roster v (fun W=>baseFold o E roster (L n W))) R.makes tiers hn (nt.le.trans tN) enough
      (half_pos positive) furls reach sp thin
  refine ⟨(sealed 0 (by simp)).1,fun mask=>WilsonSeparatedOriginalSlabBladeModule.mask (Y n) 0 (R.makes.wilson.represents N per n (nt.le.trans tN)).good (fun W=>baseFold o E roster (L n W)) ?_ mask⟩
  intro J
  exact (sealed _ (fun i=>WilsonSeparatedOriginalSlabMaskPhases.unit J i)).2

end YM.Integration.WilsonSeparatedOriginalSlabRootMarker
