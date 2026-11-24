import YM.Integration.WilsonReportHarvestRetainedSlab

/-! A base ledger reached from the true turning field can reenter the
original one-step grouping theorem on its entire original census. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabDated
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} {C:Family G} {n a t per N d k:ℕ} {D:Address.Rail C}
variable (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion) (s:Fin 3→ℕ) (q:ManyStem C o n→Body)
variable (h:C.Makes) (stock:Storage C D) (P:(j:Fin 3)→Sight C (s j) per)
variable (S:(j:Fin 3)→Emblems C (s j)) (x:(j:Fin 3)→Palette C (s j)) (roster:Census (Fin 3))
variable {B:ℕ→ℕ→ℝ} {Q:ℝ}
set_option quotPrecheck false
local notation "A" => Mine.tree o E
local notation "I" => headings o E q
local notation "J" => Mine.ward o E roster
local notation "Y" => C.path.rep N per
local notation "src" => plants (m:=a) s P S x
local notation "Λ" => (A).labelY
local notation "α" => fun j:ℕ=>(C.path.levels.budget j).supportExponent
local notation "cash" => Q*(C.S.a a/C.S.a t)
local notation "w" => RG05Readout.Many.envelope C t (d+1) k (cash)
variable {L:∀i,Config G (C.side i per)→Poly (Mine.ward o E roster i)}

include stock roster L in
theorem original (basis:∀v,Spine D B h n per (s v) N (P v) (S v))
    (na:n ≤ a) (aturn:a ≤ t) (tN:t ≤ N)
    (occupied:Occupancy o (C.path.levels.clock.J n))
    (cap:∀v:ManyStem C o n,Cap (s v.val.1+2) (q v) 1)
    (sizeBound:∀v,size (x v) ≤ Q) (hQ:1 ≤ Q) (warm:Warm C n (d+1) k)
    (degree:∀v,s v ≤ d) (history:Replay A s (le_refl n) t L N)
    (live:Integrable (L t) (prior G (C.side t per)))
    (single:∀v,Useful (Y t) (imprint h A I src t tN v))
    (upper:Ledger (Y t) (imprint h A I src t tN) (L t) ((A).supportX t)
      (fun _=>w t) (α t-4)) :
    ∀i,n ≤ i→∀it:i ≤ t, MenuBoard (Y i) (imprint h A I src i (it.trans tN)) (L i)
      ((A).supportX i) (fun _=>w i) (if i=t then α i-4 else α i) 1 := by
  let raised:=WilsonAllDateHarvestRebook.raised s S x a t
  have reserve:1 ≤ cash:=one_le_mul_of_one_le_of_one_le hQ
    ((one_le_div (C.S.a_pos _)).2 (C.S.strictAnti.antitone aturn))
  have cost (v:Fin 3):size (raised v) ≤ cash:=WilsonAllDateHarvestRebook.sizeAt (basis v) na aturn tN (sizeBound v)
  let T:=plants (m:=t) s P S raised
  let v:=Launch (m:=t) s S raised
  have words:T=src:=WilsonAllDateHarvestRebook.singleton s S x P a t
  have nt:=na.trans aturn
  let amount:=Many.total C cash (d+1) t
  let area:=rusty C t k
  have qp:0 < cash:=zero_lt_one.trans_le reserve
  have purse:=ignite (Q:=cash) (m:=t) (N:=N) warm qp (d:=d+1) (by omega)
  have lesson:Lesson (D:=D) h s n N N per T B amount v:=by
    refine ⟨fun j=>⟨P j,S j,basis j,fun _=>rfl,fun i _ _=>nearpoints (S j) (raised j) _,fun i ni iN=>?_⟩⟩
    exact head_cost (basis j) nt tN (Nat.add_le_add_right (degree j) _) (cost j) ni iN
  have lamp:=Lesson.lights s h (lesson.revise s h (le_refl n) tN)
  obtain ⟨atBase,prepared⟩:=headlines (N:=N) o E q
  have samples:∀j:ManyStem C o n,Cap (s (Λ n j)+2) (I n j) 1:=by rw [atBase];exact cap
  have fitted:PreparedA A I n t le_rfl:=fun i ni it=>prepared i ni (it.trans_le tN)
  have reach (i:ℕ) (ni:n ≤ i):=Mine.pays o E ni occupied le_rfl
  have lowered:Toured A (Mine.ward o E roster) (le_refl n) t area k:=by
    refine ⟨fun i ni _=>(reach i ni).1,fun i ni _=>(reach i ni).2,fun i _ it=>?_⟩
    exact Cushions.straight (le_of_eq (rust_local (C:=C) (k:=k) it))
  have funded:=purse.slice (le_refl n) tN
  have paid:MenuBoard (R:=Mine.ward o E roster t) (Y t) (imprint h A I T t tN) (L t) ((A).supportX t)
      (fun _=>w t) (α t-4) 1:=by
    rw [words]
    exact ⟨live,single,upper.H,upper.K,upper.legal,upper.regular,upper.forced,upper.paid⟩
  have all:=session A s I h stock (le_refl n) tN T funded lowered lamp history
    (fun i=>(degree i).trans (Nat.le_succ _)) fitted samples (le_refl _) paid
  rw [words] at all
  exact all

end YM.Integration.WilsonReportHarvestSlabDated
