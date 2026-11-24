import YM.Integration.WilsonAllDateHarvestHistoricalReplay
import YM.Integration.WilsonAllDateHarvestRebook
import YM.Integration.WilsonAllDateHarvestPhysical
import YM.Integration.WilsonReportHarvestUpperShadow

/-! The original earlier reporting palette, its full propagated Wilson field,
and its actually issued older census give the two signed lower histories.
Each billed lower source uses the original grown palette and every true rust. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestHistoricalEntry

open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} {C:Family G} {n m a t per N:ℕ}

def Captured (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ)
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
    Replay (H:=J) A s (le_refl n) t L N ∧
    L t=(fun U=>openField (density (Y t) (rows t tN)
      (fun _ _=>0) (fun _ _=>0) U)) ∧
    ∀i,n ≤ i→∀it:i ≤ t,
      let α:=if i=t then (C.path.levels.budget i).supportExponent-4
        else (C.path.levels.budget i).supportExponent
      let w:=fun _:ManyStem C o i=>envelope C t d k Q i
      ∃ (B:WilsonAllDateHarvestStability.Ledger (Y i) (rows i (it.trans tN))
          (L i) (A.supportX i) w α)
        (Z:WilsonAllDateHarvestStability.Ledger (Y i) (rows i (it.trans tN))
          (F i (it.trans tN)) (A.supportX i) w α),
        Towed (fun _:ManyStem C o i=>(1:ℝ)) id (fun v U=>Z.H v U-B.H v U) (Y i).p.B α fee ∧
        Towed (fun _:ManyStem C o i=>(1:ℝ)) Prod.fst (fun v U=>Z.K v U-B.K v U) (Y i).p.B α fee


variable (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ) (q:ManyStem C o n→Body)
variable {D:Address.Rail C}{B:ℕ→ℕ→ℝ} {r:ℕ→ℕ}{W:Worth}
variable (h:C.Makes) (book:OPE.Package C W r D) (stock:Storage C D)
variable (P:(j:Fin 3)→Sight C (s j) per) (S:(j:Fin 3)→Emblems C (s j))
variable (x:(j:Fin 3)→Palette C (s j)) (roster:Census (Fin 3))
set_option quotPrecheck false
local notation "t₀" => m+1
local notation "A" => Mine.tree o E
local notation "I" => headings o E q
local notation "M" => Mine.ward o E roster
local notation "Y" => C.path.rep N per
local notation "T" => plants (m:=a) s P S x
local notation "rows" => imprint h A I T
local notation "f" => WilsonAllDateHarvestPhysical.columns o E s q S x a N
local notation "Ξ" => fun (i:ℕ) (iN:i ≤ N)=>gust C.path N per N (birth (M i) (Y N) (f i)) i iN

include book stock in
theorem original (simple:G.Simple) {d k:ℕ} (basis:∀j:Fin 3,Spine D B h n per (s j) N (P j) (S j))
    (nm:n ≤ m) (na:n ≤ a) (aturn:a ≤ t₀) (tN:t₀ ≤ N)
    (occ:Occupancy o (C.path.levels.clock.J n))
    (cap:∀j:ManyStem C o n,Cap (s ((A).labelY n j)+2) (q j) 1)
    {Q:ℝ} (one:1 ≤ Q) (sizes:∀j,size (x j) ≤ Q)
    (warm:Warm C n (d+1) k) (degree:∀j,s j ≤ d)
    (clear:Clearance o E s I roster a) (useful:∀j,Useful (Y t₀) (rows t₀ tN j))
    {δ fee:ℝ} (pos:0 < δ) (small:δ ≤ 1) (ep:0 < fee)
    (budget:δ*(WilsonAllDateHarvestIntervalPrice.bill C n t₀ (d+1) k
      (Q*(C.S.a a/C.S.a t₀)))^3 ≤ fee/2)
    (H:Support (C.side t₀ per)→ Config G (C.side t₀ per)→Poly (Mine.masts o E na (barren o E roster a) t₀))
    (K:Box (C.side t₀ per)→ Config G (C.side t₀ per)→Poly (Mine.masts o E na (barren o E roster a) t₀))
    (files:Carton ((A).supportX t₀) H K (Y t₀).p.threshold)
    (field:(fun U=>narrow (WilsonMixedTaggedSeparatedBoard.admitted o E roster na aturn) (Ξ t₀ tN U)) =
      density (Y t₀) (rows t₀ tN) H K)
    (reg:Towed (fun _:ManyStem C o t₀=>1) id H (Y t₀).p.B ((C.path.levels.budget t₀).supportExponent-1) δ)
    (hard:Towed (fun _:ManyStem C o t₀=>1) Prod.fst K (Y t₀).p.B ((C.path.levels.budget t₀).supportExponent-1) δ) :
    Captured o E s q h P S x roster na aturn tN (d+1) k (Q*(C.S.a a/C.S.a t₀)) fee := by
  let raised := WilsonAllDateHarvestRebook.raised s S x a t₀
  let cash:=Q*(C.S.a a/C.S.a t₀)
  have oneCash : 1 ≤ cash :=
    one_le_mul_of_one_le_of_one_le one ((one_le_div (C.S.a_pos t₀)).2 (C.S.strictAnti.antitone aturn))
  have bought (j:Fin 3):size (raised j) ≤ cash := WilsonAllDateHarvestRebook.sizeAt (basis j) na aturn tN (sizes j)
  have rowsEq:plants (m:=t₀) s P S raised=T:=WilsonAllDateHarvestRebook.singleton s S x P a t₀
  have colsEq:WilsonMixedTaggedFields.columns o E s q S raised t₀ N=f:=
    WilsonAllDateHarvestRebook.columns s S x o E q a t₀ N
  have nt:=nm.trans m.le_succ
  obtain ⟨source,history,known,_⟩:=WilsonMixedTaggedFields.program (m:=t₀) o E s q S raised roster
    h book stock P nt tN basis occ cap bought (zero_lt_one.trans_le oneCash) warm degree
  have gate (z:(M t₀).Mode) (missing:z.val∉(Mine.masts o E na (barren o E roster a) t₀).choices)
      (alive:Disjoint (shadow A s I t₀) (z.val:Set _)):False :=
    missing (WilsonReportHarvestUpperShadow.restored o E s q roster na aturn clear z alive)
  have ready:=WilsonAllDateHarvestHistoricalReplay.original o E s q h stock P S raised roster
    simple basis nm tN occ cap bought oneCash warm degree na aturn gate history known
    (by rw [rowsEq];exact useful) δ pos small ep budget H K files (by rw [rowsEq,colsEq];exact field) reg hard
  have hr:scaled (0:ℂ) H=(fun _ _=>0):=by funext j U;exact zero_smul ℂ (H j U)
  have hk:scaled (0:ℂ) K=(fun _ _=>0):=by funext j U;exact zero_smul ℂ (K j U)
  rw [rowsEq,colsEq,hr,hk] at ready
  exact ready

end YM.Integration.WilsonAllDateHarvestHistoricalEntry
