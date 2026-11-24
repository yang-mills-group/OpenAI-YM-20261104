import YM.Integration.WilsonReportHarvestSlabDated
import YM.Integration.WilsonReportHarvestSlabFold

/-! The actual folded signed retained field at capture, using the same
trajectory, the same imprinted rows, and the actual cutoff palette. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabResident
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

theorem original {n a t N per d kHigh kLow:ℕ} (na:n≤a) (aturn:a≤t) (nt:n<t) (tN:t≤N)
    (stock:Storage C R.doors) (tiers:Cater C R.doors) {B:ℕ→ℕ→ℝ}
    (s:Fin 3→ℕ) (S:(i:Fin 3)→Emblems C (s i)) (P:(i:Fin 3)→Sight C (s i) per)
    (x:(i:Fin 3)→Palette C (s i)) (o:Fin 3→Site ((C).side n per)) (E:Fin 3→Motion)
    (q:ManyStem C o n→Body) (roster:Census (Fin 3))
    (basis:∀i,Spine R.doors B R.makes n per (s i) N (P i) (S i))
    (occ:Occupancy o ((C).path.levels.clock.J n)) (cap:∀i:ManyStem C o n,Cap (s i.val.1+2) (q i) 1)
    {Q δ:ℝ} (one:1≤Q) (sizes:∀i,size (x i)≤Q) (warm:Warm C n (d+1) kLow)
    (degree:∀i,s i≤d) (pos:0<δ)
    (retained:WilsonReportHarvestReplayPhysical.Retained R na aturn tN s S P x o E q roster d kHigh Q δ)
    {L:∀i,Config G ((C).side i per)→Poly (Mine.ward o E roster i)}
    (row:Replay (Mine.tree o E) s (le_refl n) t L N) :
    let A:=Mine.tree o E
    let I:=headings o E q
    let src:=plants (m:=a) s P S x
    let im:=fun j (jN:j≤N)=>imprint R.makes A I src j jN
    let Y:=(C).path.rep N per
    let opened:=WilsonAllDateHarvestEndpointOpening.opening
      (WilsonMixedTaggedSeparatedBoard.admitted o E roster na aturn) (shadow A s I t)
    let cash:=Q*((C).S.a a/(C).S.a t)
    let w:=RG05Readout.Many.envelope C t (d+1) kLow cash
    let α:=(C).path.levels.budget t|>.supportExponent
    let σ:=Many.crust C t n d kLow cash
    let source:=fun U=>baseFold o E roster (L n U)
    L t=(fun U=>opened (density (Y t) (im t tN) (fun _ _=>0) (fun _ _=>0) U)) →
      Ledger (Y t) (im t tN) (L t) (A.supportX t) (fun _=>w t) (α-4) →
      0<σ ∧ Integrable source (prior G ((C).side n per)) ∧ ∃price:ℝ,
        Furls (C).path.levels n price ∧ Alcove (Y n) ((im n (nt.le.trans tN))∘(Mine.remap o E).symm)
           source o (fun _=>σ) price (Bandage.renal (C).path.levels n) (1/2) := by
  intro A I src im Y opened cash w α σ source top upper
  have live:=WilsonReportHarvestSlabAdmission.original R na aturn nt tN stock
    s S P x o E q roster basis occ cap one sizes warm degree pos retained
  have entry:Integrable (L t) (prior G ((C).side t per)):=by rw [top];exact live
  obtain ⟨_,initial,_,_,_,_,_,_,_,_⟩:=retained
  have next:=WilsonReportHarvestSlabDated.original o E s q R.makes stock P S x roster basis
    na aturn tN occ cap sizes one warm degree row entry initial.fettled upper (n+1) n.le_succ nt
  let raised:=WilsonAllDateHarvestRebook.raised s S x a t
  have names:plants (m:=t) s P S raised=plants (m:=a) s P S x:=
    WilsonAllDateHarvestRebook.singleton s S x P a t
  rw [←names] at next
  have costs (v:Fin 3):size (raised v)≤cash:=WilsonAllDateHarvestRebook.sizeAt (basis v) na aturn tN (sizes v)
  have liveCash:0<cash:=mul_pos (zero_lt_one.trans_le one) (div_pos ((C).S.a_pos _) ((C).S.a_pos _))
  obtain ⟨base,prepared⟩:=headlines (N:=N) o E q
  have baseCap:∀v:ManyStem C o n,Cap (s ((A).labelY n v)+2) (I n v) 1:=by
    change ∀v:ManyStem C o n,Cap (s v.val.1+2) (headings o E q n v) 1
    rw [base]
    exact cap
  obtain ⟨positive,integrable,cost,furls,invoice⟩:=WilsonReportHarvestSlabFold.original
    o E s (headings o E q) R.makes tiers P S raised basis nt tN occ prepared baseCap
      costs liveCash warm degree next row
  rw [names] at invoice
  exact ⟨positive,integrable,cost,furls,invoice⟩

end YM.Integration.WilsonReportHarvestSlabResident
