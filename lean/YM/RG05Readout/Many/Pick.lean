import YM.RG05Readout.Many.Ramp
/-!
# Before capture

On real path proves pricing estimate for calibrated multi-insertion density
through all levels down to n (including at n), provided h-relative profile
parents above and before capture chosen with explicit tickets. This is at
arbitrary tuning m; `Pencil` basis chose physical matrix before test, tested
on native cell. Exact measured units and conditional product. In `dock`,
with Profile palette normalized at m, the inverse over N has already been
paid; e^o cost lives on the marked polynomial. Use together with `rust_end`
for at capturing size. Hull repayment uses SUPPORT separation (anchors in b
cells, and coalescing after those); product/counterterm continuities require
that geometry. Not asserting all-profile hierarchy smoothness here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{W:Type}[DecidableEq W][Fintype W]
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {k g:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "Y"=> C.path.rep N p
local notation "L!"=> C.path.levels.clock.op
local notation "ζ"=> Legato.Bandage.fly C.path.levels
local notation "λ₁"=> far C.path.levels
variable (o:W→Site (C.side n p)) (E:W→Motion) (s:W→ℕ) (I:∀ i:ℕ,ManyStem C o i→Body)
local notation "V'"=> ManyStem C o
local notation "A'"=> Mine.tree o E
local notation "Λ"=>(A').labelY
local notation "Φ"=>(A').narrows
local notation "H!"=> Mine.ward o E
local notation "r₀"=>(A').supportX
variable (h:C.Makes) (L:OPE.Package C w r D) (hw:Storage C D)
variable {v:(i:W)→ℕ→Palette C (s i)} {T:Pens C p W} {f q:ℕ→ℝ}{B:ℕ→ℕ→ℝ}{Q:ℝ}
    {Λ':Census W} {F:∀ i:ℕ, Config G (C.side i p)→Poly (Mine.ward o E Λ' i)}

variable (P:(i:W)→ Sight C (s i) p) (S:(i:W)→Emblems C (s i)) (x:(i:W)→Palette C (s i))
def Launch := fun j=> Many.point (S j) (x j) m
def plants := stages s P (Launch (m:=m) s S x)
local notation "V₀"=> Launch (m:=m) s S x
local notation "T!"=> plants (m:=m) s P S x
local notation "λ₀"=> fun i : V' N=>stepUp ((A').motion (Λ N i)) (r₀ N i) (entrance C (s (Λ N i)) N p (V₀ (Λ N i) N) 0 (I N i))
local notation "M"=> fun i=> if i=m then (t₁ i).supportExponent-4 else (t₁ i).supportExponent
-- simple geometry departure still assumed via Clearance, addressed seam provided by planner.

def envelope (C:Family G)(m d k:ℕ)(Q:ℝ)(i:ℕ):=west C (total C Q d m) (rusty C m k) k i

include h hw L
set_option maxHeartbeats 550000 in
lemma docks (H:∀ i:W,Spine D B h n p (s i) N (P i) (S i)) (hk:n ≤ m)(hm:m ≤ N)(ho:Occupancy o ((K).J n))
    (hc:Clearance o E s I Λ' m) (hp:PreparedA A' I n N le_rfl) (hQ:∀ j: V' n, Cap (s (Λ n j)+2) (I n j) 1)
    (hX:∀ i:W,size (x i) ≤ Q) (hy:0 < Q)
    (ht:Warm C n (d+1) k) (hS:∀ i:W,s i ≤ d)
    (hF:F N=birth (Mine.ward o E Λ' N) (Y N) λ₀) (hr:Replay A' s (H:=H! Λ') (le_refl n) N F N):
    ∀ i:ℕ,n≤ i→∀ hN:i≤ m, MenuBoard (R:= H! Λ' i) (Y i) (imprint h A' I T! i (hN.trans hm)) (F i) (r₀ i) (fun _=>envelope C m (d+1) k Q i) (M i) 1:=by
    let v':= Many.total C Q (d+1) m; let f':=rusty C m k
    have he:= ignite (Q:=Q) (m:=m) (N:=N) ht hy (d:=d+1) (by omega); have hL: Lesson (D:=D) h s n N N p T! B v' V₀:=by
       refine ⟨fun i=>⟨P i,S i,H i,fun _=>rfl,fun j _ _=>nearpoints (S i) (x i) _,fun j hj hk'=>?_⟩⟩
       exact head_cost (H i) hk hm (Nat.add_le_add_right (hS i) _) (hX i) hj hk'
    refine anchored o E s I h L hw hk hm ho hc (fun i hg _=>?_) (fun i hi hb=> (rust_local (k:=k) (C:=C) hb).le) he hL (fun i hi=> (ht.lanes _ hi).trans (hk.trans hm)) (fun i=>(hS i).trans d.le_succ) hQ hp (fun i hv=> ht.buys i _ hv (hk.trans hm)) hF hr
    rw [rust_above hg,rust_above (hg.trans i.le_succ)]

-- `Replay F N` exists for every trajectory. Choosing F ranger independently.
omit h hw L in
lemma wind (hk:n ≤ N) {B: Census W} (T:Config G (C.side N p)→ Poly (H! B N)):∃ F',Replay (H:=H! B) A' s (le_refl n) N F' N∧ F' N=T:=
    reels_write A' s le_rfl hk (fun _ h _=>Mine.wardlight _ _ _ h) T N
-- roots gives pulls on all heights. explicitly constructed.
noncomputable def headings (b: ManyStem C o n→Body) (i:ℕ): V' i→ Body:= if h:n ≤ i then Nat.leRec (motive:=fun i _=>ManyStem C o i→Body) b (fun {i} h f x=> let e:=(Mine.tree o E).narrows i h; headFee C p i (e x).2 (f (e x).1)) h else 0
omit h hw L [DecidableEq W][Fintype W] in
lemma headlines (b: ManyStem C o n→Body):headings o E b n=b∧PreparedA A' (headings o E b) n N le_rfl:=by
    refine ⟨?_,fun i hi h x=>?_⟩
    · rw [headings,dif_pos le_rfl,Nat.leRec_self]
    unfold headings; rw [dif_pos (hi.trans i.le_succ),Nat.leRec_succ (h1:=hi),dif_pos hi]
end YM.RG05Readout.Many
