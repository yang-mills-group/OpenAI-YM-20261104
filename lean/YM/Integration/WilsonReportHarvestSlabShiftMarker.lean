import YM.Integration.WilsonReportHarvestSlabShiftSingle
import YM.Integration.WilsonReportHarvestSlabResident

/-! Fold either issued Wilson history on its genuine adjacent board and
group its actual raw three-name field into one paid mark. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabShiftMarker
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
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
    (degree:∀i,s i≤d) (hn:0<n)
    (reach:∀v:Fin 3,coverNumber (((C).path.levels.budget n).B)
      ({o 0,o v}:Support ((C).side n per)) ≤ Ribbons.peepers (C).path.levels n) :
    let roster:=Stock.census (Fin 3)
    let A:=Mine.tree o E
    let I:=headings o E q
    let src:=plants (m:=a) s P S x
    let Y:=(C).path.rep N per
    let cash:=Q*((C).S.a a/(C).S.a t)
    let w:=RG05Readout.Many.envelope C t (d+1) kLow cash
    let price:=Many.fee C t n d kLow 3 cash
    ∀ (L:∀i,Config G ((C).side i per)→Poly (Mine.ward o E roster i)),
      Replay A s (le_refl n) t L N →
      MenuBoard (Y (n+1)) (imprint R.makes A I src (n+1) (nt.trans_le tN)) (L (n+1))
        (A.supportX (n+1)) (fun _=>w (n+1))
        (if n+1=t then ((C).path.levels.budget (n+1)).supportExponent-4
         else ((C).path.levels.budget (n+1)).supportExponent) 1 →
      Integrable (fun U=>baseFold o E roster (L n U)) (prior G ((C).side n per)) ∧
      (∀U,(baseFold o E roster (L n U)).part roster.quiet=(Y n).eval U) ∧
      (∀i U,(baseFold o E roster (L n U)).part (roster.fire i)=
        (imprint R.makes A I src n (nt.le.trans tN) ((Mine.remap o E).symm i)).1 U) ∧
      ∀v:Fin 3→ℂ,(∀i,‖v i‖≤1) →
      0<price ∧ ∃new:Three G ((C).side n per), Useful (Y n) new ∧
        (∀U,new.1 U=(WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E roster (L n U))).part WilsonReportHarvestSlabLabels.entire) ∧
        MergeProof.Float.Blade (Y n) (o 0) new.2.1 (profile (Y n).activities new.2.2) 0 (4*(1/price)) := by
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
  obtain ⟨positive,integrable,_,furls,invoice⟩:=WilsonReportHarvestSlabFold.original
    o E s (headings o E q) R.makes tiers P S raised basis nt tN occ prepared baseCap
      costs liveCash warm degree next row
  rw [names] at invoice
  refine ⟨integrable,invoice.value,invoice.tally,?_⟩
  intro v bounded
  exact WilsonReportHarvestSlabShiftSingle.original (N:=N) R.makes tiers hn (nt.le.trans tN)
    occ positive integrable furls invoice reach v bounded

end YM.Integration.WilsonReportHarvestSlabShiftMarker
