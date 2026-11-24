import YM.Integration.WilsonReportHarvestEarlierSlab
import YM.Integration.WilsonReportHarvestSlabAdmission

/-! The charged earlier comparator is the original normalized Wilson conditional
of the full imprinted reference at its one genuine turning date. The comparisons
of the two regular and forced ledgers hold for the very same lower field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestRetainedSlab
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} {C:Family G} {n m a t per N:ℕ}

def Settled (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ)
    (q:ManyStem C o n→Body) (h:C.Makes) (P:(j:Fin 3)→Sight C (s j) per)
    (S:(j:Fin 3)→Emblems C (s j)) (x:(j:Fin 3)→Palette C (s j))
    (roster:Census (Fin 3)) (na:n ≤ a) (aturn:a ≤ t) (tN:t ≤ N) (d k:ℕ) (Q fee:ℝ) : Prop :=
  let A:=Mine.tree o E
  let J:=Mine.ward o E roster
  let Y:=C.path.rep N per
  let I:=headings o E q
  let T:=plants (m:=a) s P S x
  let rows:=fun i (iN:i ≤ N)=>imprint h A I T i iN
  let f:=WilsonAllDateHarvestPhysical.columns o E s q S x a N
  let F:=fun i (iN:i ≤ N)=>gust C.path N per N (birth (J i) (Y N) (f i)) i iN
  let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster na aturn
  let openField:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow A s I t)
  ∃ L:∀i,Config G (C.side i per)→Poly (J i),
    ∃ row:Replay (H:=J) A s (le_refl n) t L N,
    L t=(fun U=>openField (density (Y t) (rows t tN)
      (fun _ _=>0) (fun _ _=>0) U)) ∧
    (∀i (ni:n ≤ i) (it:i ≤ t) (U:Config G (C.side i per)),
      ((Y i).eval U)⁻¹ • L i U =
        actualTransport C (N:=N) (fun W=>((Y t).eval W)⁻¹ •
          WilsonReportHarvestEarlierSlab.route row i ni it
            (openField (density (Y t) (rows t tN) (fun _ _=>0) (fun _ _=>0) W))) it U) ∧
    ∀i,n ≤ i→∀it:i ≤ t,
      let α:=if i=t then (C.path.levels.budget i).supportExponent-4
        else (C.path.levels.budget i).supportExponent
      let w:=fun _:ManyStem C o i=>RG05Readout.Many.envelope C t d k Q i
      ∃ (B:WilsonAllDateHarvestStability.Ledger (Y i) (rows i (it.trans tN))
          (L i) (A.supportX i) w α)
        (Z:WilsonAllDateHarvestStability.Ledger (Y i) (rows i (it.trans tN))
          (F i (it.trans tN)) (A.supportX i) w α),
        Towed (fun _:ManyStem C o i=>(1:ℝ)) id (fun v U=>Z.H v U-B.H v U) (Y i).p.B α fee ∧
        Towed (fun _:ManyStem C o i=>(1:ℝ)) Prod.fst (fun v U=>Z.K v U-B.K v U) (Y i).p.B α fee

theorem received (made:C.Makes) {o:Fin 3→Site (C.side n per)} {E:Fin 3→Motion} {s:Fin 3→ℕ}
    {q:ManyStem C o n→Body} {h:C.Makes} {P:(v:Fin 3)→Sight C (s v) per}
    {S:(v:Fin 3)→Emblems C (s v)} {x:(v:Fin 3)→Palette C (s v)}
    {roster:Census (Fin 3)} {na:n ≤ a} {aturn:a ≤ t} {tN:t ≤ N} {d k:ℕ} {Q fee:ℝ}
    (sale:WilsonAllDateHarvestHistoricalEntry.Captured o E s q h P S x roster na aturn tN d k Q fee)
    (live:let A:=Mine.tree o E
          let shifts:=headings o E q
          let marks:=imprint h A shifts (plants (m:=a) s P S x) t tN
          let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster na aturn
          let gate:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow A s shifts t)
          Integrable (fun W=>gate (density (C.path.rep N per t) marks (fun _ _=>0) (fun _ _=>0) W))
            (prior G (C.side t per))) :
    Settled o E s q h P S x roster na aturn tN d k Q fee := by
  obtain ⟨L,row,top,bill⟩:=sale
  refine ⟨L,row,top,?_,bill⟩
  have valid:Integrable (L t) (prior G _):=by rw [top];exact live
  intro j nj jt U
  let move:=WilsonReportHarvestEarlierSlab.route row j nj jt
  exact (WilsonReportHarvestEarlierSlab.normalized row made tN valid nj jt U).trans
    (congrArg (fun M:Config G (C.side t per)→Poly (Mine.ward o E roster t)=>
      actualTransport C (N:=N) (fun W=>((C.path.rep N per t).eval W)⁻¹ • move (M W)) jt U) top)

section Physical
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family

include simple in
theorem original {n a t N per d kHigh kLow:ℕ} (na:n ≤ a) (aturn:a ≤ t) (nt:n < t) (tN:t ≤ N)
    (book:OPE.Package C R.w (mutt (C).path.levels R.Q) R.doors) (stock:Storage C R.doors)
    {B:ℕ→ℕ→ℝ} (s:Fin 3→ℕ) (S:(i:Fin 3)→Emblems C (s i)) (P:(i:Fin 3)→Sight C (s i) per)
    (x:(i:Fin 3)→Palette C (s i)) (o:Fin 3→Site ((C).side n per))(E:Fin 3→Motion)
    (q:ManyStem C o n→Body)(roster:Census (Fin 3))
    (basis:∀i,Spine R.doors B R.makes n per (s i) N (P i) (S i))
    (occ:Occupancy o ((C).path.levels.clock.J n))
    (cap:∀i:ManyStem C o n,Cap (s i.val.1+2) (q i) 1)
    {Q δ fee:ℝ} (one:1 ≤ Q) (size:∀i,size (x i) ≤ Q)
    (warm:Warm C n (d+1) kLow) (degree:∀i,s i ≤ d)
    (clear:Clearance o E s (headings o E q) roster a)
    (pos:0 < δ) (small:δ ≤ 1) (ep:0 < fee)
    (budget:δ*(WilsonAllDateHarvestIntervalPrice.bill C n t (d+1) kLow
      (Q*((C).S.a a/(C).S.a t)))^3 ≤ fee/2)
    (retained:WilsonReportHarvestReplayPhysical.Retained R na aturn tN s S P x o E q roster d kHigh Q δ) :
    Settled o E s q R.makes P S x roster na aturn tN
      (d+1) kLow (Q*((C).S.a a/(C).S.a t)) fee := by
  have sale:=WilsonAllDateHarvestRetainedCapture.original R simple na aturn nt tN book stock
    s S P x o E q roster basis occ cap one size warm degree clear pos small ep budget retained
  exact received R.makes sale (WilsonReportHarvestSlabAdmission.original R na aturn nt tN stock
    s S P x o E q roster basis occ cap one size warm degree pos retained)

end Physical
end YM.Integration.WilsonReportHarvestRetainedSlab
