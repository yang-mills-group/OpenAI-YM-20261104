import YM.Integration.WilsonAllDateHarvestCourseEntry
import YM.Integration.WilsonAllDateHarvestMeasuredOpening
import YM.Integration.WilsonAllDateHarvestReplay

/-! The actual reporting input is restored at its turning date and replayed
down the original Wilson history. The stripped comparison keeps the old vacuum,
forced activities, and every measured singleton. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestPhysicalReplay

open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} {C:Family G} {n m per N d k:ℕ} {D:Address.Rail C}
variable (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ) (q:ManyStem C o n→Body)
variable (h:C.Makes) (stock:Storage C D) (P:(j:Fin 3)→Sight C (s j) per)
variable (S:(j:Fin 3)→Emblems C (s j)) (x:(j:Fin 3)→Palette C (s j)) (roster:Census (Fin 3))
variable {B:ℕ→ℕ→ℝ} {Q:ℝ}
set_option quotPrecheck false
local notation "t" => (m+1)
local notation "A" => Mine.tree o E
local notation "Λ" => (A).labelY
local notation "I" => headings o E q
local notation "H" => Mine.ward o E roster
local notation "Y" => C.path.rep N per
local notation "T" => plants (m:=t) s P S x
local notation "v" => Launch (m:=t) s S x
local notation "rows" => imprint h A I T
local notation "cols" => WilsonMixedTaggedFields.columns o E s q S x t N
local notation "full" => fun (i:ℕ) (iN:i ≤ N)=>
  gust C.path N per N (birth (H i) (Y N) (cols i)) i iN
local notation "w₀" => envelope C t (d+1) k Q
local notation "α" => fun i:ℕ=>(C.path.levels.budget i).supportExponent
local notation "e" => fun i:ℕ=>if i=t then (α i)-4 else (α i)

include stock in
theorem original (basis:∀j:Fin 3,Spine D B h n per (s j) N (P j) (S j))
    (nm:n ≤ m) (tN:t ≤ N) (occupied:Occupancy o (C.path.levels.clock.J n))
    (cap:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (q j) 1)
    (sizeBound:∀j:Fin 3,size (x j) ≤ Q) (hQ:1 ≤ Q)
    (warm:Warm C n (d+1) k) (degree:∀j:Fin 3,s j ≤ d)
    (clear:Clearance o E s I roster t)
    {X:∀i,Config G (C.side i per)→Poly (H i)}
    (source:Replay A s (le_refl n) N X N)
    (knownSource:∀i,n ≤ i→∀iN:i ≤ N,X i=full i iN ∧
      ∀U (a:((H i).Mode)),¬Disjoint (shadow A s I i) (a.val:Set _)→(X i U).part a=0)
    (single:∀j,Useful (Y t) (rows t tN j))
    (δ:ℝ) (positive:0 < δ) (small:δ ≤ 1)
    (R:Support (C.side t per)→ Config G (C.side t per)→
      Poly (Mine.masts o E (nm.trans m.le_succ) (barren o E roster t) t))
    (K:Box (C.side t per)→ Config G (C.side t per)→
      Poly (Mine.masts o E (nm.trans m.le_succ) (barren o E roster t) t))
    (legal:Carton ((A).supportX t) R K (Y t).p.threshold)
    (originalField:(fun U=>narrow (WilsonMixedTaggedSeparatedBoard.admitted o E roster (nm.trans m.le_succ) le_rfl)
      (full t tN U))=density (Y t) (rows t tN) R K)
    (regular:Towed (fun _:ManyStem C o t=>1) id R (Y t).p.B ((α t)-1) δ)
    (forced:Towed (fun _:ManyStem C o t=>1) Prod.fst K (Y t).p.B ((α t)-1) δ) :
    let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster (nm.trans m.le_succ) (le_refl t)
    let opened:=WilsonAllDateHarvestEndpointOpening.opening inc (shadow A s I t)
    ∃ L:∀i,Config G (C.side i per)→Poly (H i), Replay A s (le_refl n) t L N ∧
      L t=(fun U=>opened (density (Y t) (rows t tN) (scaled 0 R) (scaled 0 K) U)) ∧
      ∀i,n ≤ i→∀it:i ≤ t,
        ∃ (base:Ledger (Y i) (rows i (it.trans tN)) (L i) ((A).supportX i) (fun _=>w₀ i) (e i))
          (actual:Ledger (Y i) (rows i (it.trans tN)) (full i (it.trans tN)) ((A).supportX i)
            (fun _=>w₀ i) (e i)),
          Towed (fun _:ManyStem C o i=>w₀ i) id (fun j U=>actual.H j U-base.H j U)
            (Y i).p.B (e i) (2*δ) ∧
          Towed (fun _:ManyStem C o i=>w₀ i) Prod.fst (fun j U=>actual.K j U-base.K j U)
            (Y i).p.B (e i) (2*δ) := by
  intro inc opened
  let amount:=Many.total C Q (d+1) t
  let area:=rusty C t k
  have nt:=nm.trans m.le_succ
  have qp:0 < Q:=zero_lt_one.trans_le hQ
  have purse:=ignite (Q:=Q) (m:=t) (N:=N) warm qp (d:=d+1) (by omega)
  have lesson:Lesson (D:=D) h s n N N per T B amount v:=by
    refine ⟨fun j=>⟨P j,S j,basis j,fun _=>rfl,fun i _ _=>nearpoints (S j) (x j) _,fun i ni iN=>?_⟩⟩
    exact head_cost (basis j) nt tN (Nat.add_le_add_right (degree j) _) (sizeBound j) ni iN
  have lamp:=Lesson.lights s h (lesson.revise s h (le_refl n) tN)
  obtain ⟨start,prepared⟩:=headlines (N:=N) o E q
  have samples:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (I n j) 1:=by rw [start];exact cap
  have fitted:PreparedA A I n t le_rfl:=fun i ni it=>prepared i ni (it.trans_le tN)
  have reach (i:ℕ) (ni:n ≤ i):=Mine.pays o E ni occupied le_rfl
  have lowered:Toured A (H) (le_refl n) t area k:=by
    refine ⟨fun i ni _=>(reach i ni).1,fun i ni _=>(reach i ni).2,fun i _ it=>?_⟩
    exact Cushions.straight (le_of_eq (rust_local (C:=C) (k:=k) it))
  have funded:=purse.slice (le_refl n) tN
  obtain ⟨left,right,affine⟩:=WilsonAllDateHarvestCourseEntry.original A s I h stock (le_refl n) nm
    (Nat.lt_of_succ_le tN) funded lamp fitted samples (reach m nm).2 single
    (WilsonAllDateHarvestCourseEntry.tuning C t (d+1) k hQ)
    (WilsonAllDateHarvestAffine.actual o E roster nt le_rfl) δ positive legal regular forced
  have wpos:0 < w₀ t:=mul_pos (rust_paid _).1 (grantw (totalpos qp t))
  obtain ⟨F,replay,known,base,up,picture⟩:=WilsonAllDateHarvestMeasuredOpening.original
    o E s q S x roster h nt tN source knownSource lesson clear (fun _=>wpos) left right (δ:ℂ)
    (fun U=>congr_fun (originalField.trans affine) U)
  obtain ⟨L,run,initial,paid⟩:=WilsonAllDateHarvestReplay.original A (H) s I h stock (le_refl n)
    nt tN funded lowered lamp replay (fun i=>(degree i).trans d.le_succ) fitted samples (by linarith only)
    base up δ positive.le small picture (fun i _ _=>WilsonAllDateHarvestReplay.ward o E roster i)
  refine ⟨L,run,initial,?_⟩
  intro i ni it
  let price (Z:Config G (C.side i per)→Poly (H i)) : Prop :=
    ∃ (base:Ledger (Y i) (rows i (it.trans tN)) (L i) ((A).supportX i) (fun _=>w₀ i) (e i))
      (actual:Ledger (Y i) (rows i (it.trans tN)) Z ((A).supportX i) (fun _=>w₀ i) (e i)),
      Towed (fun _:ManyStem C o i=>w₀ i) id (fun j U=>actual.H j U-base.H j U)
        (Y i).p.B (e i) (2*δ) ∧
      Towed (fun _:ManyStem C o i=>w₀ i) Prod.fst (fun j U=>actual.K j U-base.K j U)
        (Y i).p.B (e i) (2*δ)
  exact Eq.mp (congrArg price (known i ni (it.trans tN))) (paid i ni it)

end YM.Integration.WilsonAllDateHarvestPhysicalReplay
