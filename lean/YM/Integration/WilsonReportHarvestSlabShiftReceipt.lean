import YM.Integration.WilsonReportHarvestSlabShiftPhysical
/-! The physical signed coefficient and its genuine retained source,
at the original reporting age, with an unweighted price. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabShiftReceipt
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} (R:Run G)
set_option quotPrecheck false
local notation "C" => R.family

def Captured {b a t N per:ℕ} (na:b+1 ≤ a) (aturn:a ≤ t) (nt:b+1 < t) (top:t ≤ N)
    (s:Fin 3→ℕ) (S:(i:Fin 3)→Emblems C (s i)) (P:(i:Fin 3)→Sight C (s i) per)
    (x:(i:Fin 3)→Palette C (s i)) (o:Fin 3→Site ((C).side (b+1) per)) (E:Fin 3→Motion)
    (q:ManyStem C o (b+1)→Body) (target:ℝ):Prop :=
    let n:=b+1
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
    ∃ L:∀j,Config G ((C).side j per)→Poly (J j),∃route:Replay A s (le_refl n) t L N,
      L t=inlet ∧
      (∀j (nj:n ≤ j) (jt:j ≤ t) V, ((Y j).eval V)⁻¹ • L j V=
        actualTransport C (N:=N) (fun W=>((Y t).eval W)⁻¹ •
          WilsonReportHarvestEarlierSlab.route route j nj jt (inlet W)) jt V) ∧
      Integrable (fun V=>baseFold o E roster (L n V)) (prior G ((C).side n per)) ∧
      (∀V,(baseFold o E roster (real V)).part roster.quiet=(baseFold o E roster (L n V)).part roster.quiet) ∧
      (∀i V,(baseFold o E roster (real V)).part (roster.fire i)=(baseFold o E roster (L n V)).part (roster.fire i)) ∧
      ∀v:Fin 3→ℂ,(∀i,‖v i‖≤1) → ∃cost:ℝ,∃X:Coefficient ((C).labels.level 0) ((C).side b per),
        X.Format 0 (C).params (Y b) ∧ X.remBound 0 (Y b) (kappa (C).path b) cost ∧
        ((C).labels.level 0).coeffSize X.x ≤ cost ∧ cost ≤ target ∧
        ∀u (age:u ≤ b),WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age X=
          pushTo (C).path N per (age.trans b.le_succ)
            (fun W=>(WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E roster (real W))).part entire-
              (WilsonReportHarvestSlabShiftLabels.translated v (baseFold o E roster (L n W))).part entire)
            1/liftVac (C).path N per u 1

theorem original {b a t N per d kHigh kLow:ℕ} (na:b+1 ≤ a) (aturn:a ≤ t) (nt:b+1 < t) (top:t ≤ N)
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
      ({o 0,o i}:Support ((C).side (b+1) per)) ≤ peepers (C).path.levels (b+1))
    {target:ℝ} (charged:bling (C).path.levels b*(2*δ*(4*(1/Many.fee C t (b+1) d kLow 3
      (Q*((C).S.a a/(C).S.a t))))) ≤ target):
    Captured R na aturn nt top s S P x o E q target := by
  cases t with
  | zero=>omega
  | succ t=>
    obtain ⟨L,route,head,transport,live,quiet,singles,signed⟩:=
      WilsonReportHarvestSlabShiftPhysical.original R na aturn nt top book stock tiers s S P x o E q basis
        occ cap one sizes warm degree clear pos held eligible home reach
    refine ⟨L,route,head,transport,live,quiet,singles,fun v bound=>?_⟩
    obtain ⟨_,X,format,rem,size,read⟩:=signed v bound
    exact ⟨_,X,format,rem,size,charged,read⟩

end YM.Integration.WilsonReportHarvestSlabShiftReceipt
