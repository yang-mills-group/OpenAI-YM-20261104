import YM.Integration.WilsonAllDateHarvestPhysicalReplay
import YM.Integration.WilsonAllDateHarvestTurningEntry
import YM.Integration.WilsonMixedTaggedSpend

/-! On the original measured capture interval, spend a single separation radius
both at the true turning board and at every subsequent marked Wilson integral. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestObservedReplay
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} {C:Family G} {n m t N per:ℕ}

/-- The compared field starts from the full original vacuum and singleton
sectors. At every lower date the second ledger represents the true Wilson
integral of the original complete cutoff birth. -/
def Captured (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ)
    (q:ManyStem C o n→Body) (h:C.Makes) (P:(j:Fin 3)→Sight C (s j) per)
    (S:(j:Fin 3)→Emblems C (s j)) (x:(j:Fin 3)→Palette C (s j))
    (roster:Census (Fin 3)) (nt:n ≤ t) (tN:t ≤ N) (d k:ℕ) (Q fee:ℝ) : Prop :=
  let A:=Mine.tree o E
  let J:=Mine.ward o E roster
  let Y:=C.path.rep N per
  let I:=headings o E q
  let T:=plants (m:=t) s P S x
  let rows:=fun i (iN:i ≤ N)=>imprint h A I T i iN
  let f:=WilsonMixedTaggedFields.columns o E s q S x t N
  let F:=fun i (iN:i ≤ N)=>gust C.path N per N (birth (J i) (Y N) (f i)) i iN
  let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nt (le_refl t)
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

section Dates
set_option quotPrecheck false
variable (R:Run G) {d k l order:ℕ}
variable (o:Fin 3→Site (R.family.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ) (q:ManyStem R.family o n→Body)
variable (P:(j:Fin 3)→Sight R.family (s j) per) (S:(j:Fin 3)→Emblems R.family (s j))
variable (x:(j:Fin 3)→Palette R.family (s j))
variable (roster:Census (Fin 3))
local notation "t₀" => m+1
local notation "β₀" => R.family.path.levels.clock.hatBeta t₀
local notation "g₀" => (Real.sqrt (R.family.path.rep N per t₀).beta)⁻¹
local notation "A₀" => Mine.tree o E
local notation "Y₀" => R.family.path.rep N per

theorem atDates {allowance:ℕ→ℕ→ℝ} {w:Worth} {r:ℕ→ℕ}
    (book:OPE.Package R.family w r R.doors) (stock:Storage R.family R.doors)
    (basis:∀j,Spine R.doors allowance R.makes n per (s j) N (P j) (S j)) (nm:n ≤ m) (live:t₀ < N)
    (occupied:Occupancy o (R.family.path.levels.clock.J n))
    (clear:Clearance o E s (headings o E q) roster t₀)
    (cap:∀j:ManyStem R.family o n,Cap (s ((Mine.tree o E).labelY n j)+2) (q j) 1)
    {Q ε:ℝ} (Qone:1 ≤ Q) (sizes:∀j,size (x j) ≤ Q) (ceiling:Q ≤ β₀^l)
    (warm:Warm R.family n (d+1) k) (degree:∀i,s i ≤ d) (ep:0 < ε) {D:ℕ}
    (room:D*(4*(R.family.path.levels.budget t₀).B+2)+2*(R.family.path.levels.budget t₀).B ≤
      (R.family.path.levels.budget t₀).B^2)
    (admit:β₀^((k+l)*3)*Real.exp (-(D:ℝ)) ≤ 1)
    (pay:∀i,n ≤ i→i ≤ t₀→∀z:(Mine.ward o E roster i).Mode,
      β₀^((k+l)*3)*Real.exp (-(D:ℝ)) ≤ ((ε/2)*g₀^order)*
        Poly.toll (fun _:ManyStem R.family o i=>envelope R.family t₀ (d+1) k Q i) z):
    Captured o E s q R.makes P S x roster (nm.trans (Nat.le_succ m)) live.le (d+1) k Q (ε*g₀^order) := by
  let C:=R.family
  have nt:n ≤ t₀:=nm.trans (Nat.le_succ m)
  have qp:0 < Q:=zero_lt_one.trans_le Qone
  let rows:=imprint R.makes A₀ (headings o E q) (plants (m:=t₀) s P S x) t₀ live.le
  let cols:=WilsonMixedTaggedFields.columns o E s q S x t₀ N
  let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nt (le_refl t₀)
  let field:=fun U=>narrow inc (gust C.path N per N
    (birth (Mine.ward o E roster t₀) (Y₀ N) (cols t₀)) t₀ live.le U)
  obtain ⟨source,history,identified,board⟩:=WilsonMixedTaggedFields.program (m:=t₀) o E s q S x roster
    R.makes book stock P nt live.le basis occupied cap sizes qp warm degree
  rw [if_neg live.ne,(identified t₀ nt live.le).1] at board
  obtain ⟨H,K,legal,head,reg,hard⟩:=WilsonAllDateHarvestTurningEntry.original R nt live.le o E roster
    qp ceiling room (d:=d+1) (k:=k) rows field board
  let δ:=β₀^((k+l)*3)*Real.exp (-(D:ℝ))
  have δp:0 < δ:=mul_pos (pow_pos (zero_lt_one.trans (C.path.levels.fits.delayed t₀)) _) (Real.exp_pos _)
  obtain ⟨L,run,start,entries⟩:=WilsonAllDateHarvestPhysicalReplay.original o E s q R.makes stock P S x roster
    basis nm live.le occupied cap sizes Qone warm degree clear history identified board.fettled δ δp admit H K legal head reg hard
  refine ⟨L,run,?_,?_⟩
  · have zr:scaled (0:ℂ) H=(fun _ _=>0):=by funext y U;exact zero_smul ℂ (H y U)
    have zk:scaled (0:ℂ) K=(fun _ _=>0):=by funext y U;exact zero_smul ℂ (K y U)
    rw [zr,zk] at start
    exact start
  intro i ni it
  obtain ⟨B,Z,reg',hard'⟩:=entries i ni it
  let w:=fun _:ManyStem C o i=>envelope C t₀ (d+1) k Q i
  have wp (v:ManyStem C o i):0 < w v:=mul_pos (rust_paid _).1 (grantw (totalpos qp i))
  have gp:0 ≤ g₀:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have total:0 ≤ (ε/2)*g₀^order:=mul_nonneg (half_pos ep).le (pow_nonneg gp _)
  have convert:2*((ε/2)*g₀^order)=ε*g₀^order:=by ring
  have a:=WilsonMixedTaggedSpend.chosen reg' wp (mul_pos (by norm_num) δp)
    (by norm_num : 0 ≤ (2:ℝ)) total (le_refl (2*δ)) (pay i ni it)
  have b:=WilsonMixedTaggedSpend.chosen hard' wp (mul_pos (by norm_num) δp)
    (by norm_num : 0 ≤ (2:ℝ)) total (le_refl (2*δ)) (pay i ni it)
  exact ⟨B,Z,convert ▸ a,convert ▸ b⟩

end Dates

end YM.Integration.WilsonAllDateHarvestObservedReplay
