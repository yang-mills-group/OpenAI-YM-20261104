import YM.OPE.Cluster.Stem
import YM.OPE.Loom.Tail
/-!
# Gather lengths in central cell and copies at any level of a main stack
From raw physical offset norms. For all possible varying positions and periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Station Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J W:Type}[Fintype I][DecidableEq I]{G:Gauge}{C:Family G}{j k N m q l p:ℕ}
local notation "A"=> C.path.levels
local notation "S"=> C.S
set_option quotPrecheck false
variable (x y : Site (C.side j p)) (o:I→ Site (C.side j p))
local notation "E"=> (loops C j p)
namespace SitePlan
lemma sails (hp:j≤k)(hq:k ≤ m) : E x m=(C.S.toDepth hq p).embed (E x k):=by rw [vect C _ _ _ _ hp, vect C _ _ _ _ (hp.trans hq)]; exact Station.embed_comp ..
lemma sails_parent (h:k ≤ m ): (C.S.toDepth h p).parent (E x m)= E x k:=by
   rcases le_total j k with hh|hh; rw [sails x hh h,Ratio.embed_parent]
   rw [vote C _ _ _ _ hh]; rcases le_total j m with hN|hN; rw [vect C _ _ _ _ hN, parent_nested (C.S.toDepth hh p) (C.S.toDepth hN p) _ (C.S.toDepth_odd _ _) (C.S.toDepth_odd _ _), Ratio.embed_parent]
   rw [vote C _ _ _ _ hN, ← parent_nested (C.S.toDepth h p) (C.S.toDepth hN p) _ (C.S.toDepth_odd _ _) (C.S.toDepth_odd _ _)]
lemma repeats (hk:k ≤ N): E x k= loops C N p (E x N) k:=by rw [vote C _ _ _ _ hk]; exact (sails_parent x hk).symm
lemma sails_pc (hk:j≤N) : C.S.place (E x N - E y N)= C.S.place (x-y):=by
   let Z:= C.S.toDepth hk p; rw [vect C _ _ _ _ hk,vect C _ _ _ _ hk]; rw [show Z.embed x - Z.embed y=Z.embed (x-y) from (map_sub Z.root ..).symm]; exact C.S.embeds_place ..
lemma sails_equal (hp:k ≤ j) (u: Site (C.side k p)) (he:x=(C.S.toDepth hp p).embed u) : loops C k p u = E x:=by
   subst x; let Z:= C.S.toDepth hp p; have ht:Z.embed u=loops C k p u j:=(vect C _ _ _ _ hp).symm; funext l; rcases le_total l j with h|h; rw [ht]; exact repeats u h -- loops using that x
   rw [ht]; exact (sails u hp h).trans (vect C _ _ _ _ h).symm
lemma loops_id : ∀ i,E 0 i=0:=by intro i; rcases le_total j i with he|he; rw [vect C _ _ _ _ he]; exact (C.S.toDepth he p).root.map_zero; rw [vote C _ _ _ _ he]; let Z:= C.S.toDepth he p; exact (show Z.parent 0=0 from Z.root.map_zero ▸ Z.embed_parent 0)
-- Upper bound on offset pair (not offset-root only). telescopes through the camp.
private lemma reach_pair (h:k ≤ j): C.S.a k*(separation (E x k) (E y k):ℝ) ≤ C.S.a k+ ‖C.S.place (x-y)‖:=by
    let Z:= C.S.toDepth h p; let B:= separation (E x k) (E y k); let n:= Z.count.val
    have hV i: 2*separation i (Z.embed (E i k))< n:=by rw [show E i k = _ from vote C j p k i h]; exact midway Z (C.S.toDepth_odd _ _) _
    have hz : separation (Z.embed (E x k)) (Z.embed (E y k)) = n*B:= Station.both ..
    have ht : n*B ≤ n+separation x y:=by have ha:= separation_triangle (Z.embed (E x k)) x (Z.embed (E y k)); rw [separation_comm (Z.embed (E x k)) x,hz] at ha; have h₁:=hV x; have h₂:=hV y; have h₃:=separation_triangle x y (Z.embed (E y k)); omega
    let a:=C.S.a k; have hy:C.S.a j*(n:ℝ)=a:=C.S.embeds_scale Z
    change a*(B:ℝ) ≤ a+_; rw [← hy,mul_assoc]; have hh:= (normC C j p (x-y)).1
    refine (mul_le_mul_of_nonneg_left (by exact_mod_cast ht : (n:ℝ)*B ≤ n+(separation x y:ℝ)) (C.S.a_pos j|>.le)).trans ?_; rw [mul_add,Loom.separation_alt]; gcongr
lemma upper_pair : C.S.a k*(separation (E x k) (E y k):ℝ) ≤ C.S.a k+ ‖C.S.place (x-y)‖:=by
   let n:= max k j; have ha:k ≤ n:= le_max_left ..; have hb:j≤n:= le_max_right ..; rw [repeats x ha,repeats y ha,← sails_pc x y hb]; exact reach_pair _ _ ha
lemma lower_pair (h:4*threshold C 100 k ≤ ‖C.S.place (x-y)‖): stride C 100 k-4 ≤ separation (E x k) (E y k):=by
   let n:= max k j; have ha:k≤n:=le_max_left ..; have hb:j≤n:=le_max_right ..; rw [repeats x ha,repeats y ha]; apply Loom.lower ha; rw [sails_pc x y hb]; apply le_trans _ h; let e:= stride C 100 k; change 2*C.S.a k*(((e-4:ℕ):ℝ)+1)≤ 4*((e:ℝ)*_); have hp: 4 ≤ e:=by unfold e stride; omega
   have hr:(4:ℝ)≤e:=by exact_mod_cast hp
   rw [Nat.cast_sub hp, Nat.cast_ofNat]; nlinarith only [mul_pos (C.S.a_pos k) (show 0<(e:ℝ) from lt_of_lt_of_le (by norm_num) hr), C.S.a_pos k] -- order

variable (h:m ≤ k)
local notation "V"=> Site (C.side m p)
local notation "f "=> (royal C m p k).place (fun i=> E (o i) k)
include h
lemma seps (u:Site (C.side m p)) (i l:I): separation ((f) (u,i)) ((f) (u,l))= separation (E (o i) k) (E (o l) k):=by simp_rw [placeR h, affine,separation_translate,separation_signed]
local notation "P"=> C.path.levels.budget
-- every player stays in charging range of their copied center; arbitrary k, measured in fixed units even for deepest events
lemma beyond_bill (hc:∀ i,8*‖C.S.place (o i)‖≤ C.S.a m) (ht:2*((P k).B^2+4) ≤ (C.S.toDepth h p).count.val) : Cross (P k).B (f):=by
   let R:= C.S.toDepth h p; let K:=R.count.val; let d:= C.S.a m; let B:=(P k).B
   have he(i): 2*separation (E (o i) k) 0 ≤ K-B^2:=by
       have hx:= upper_pair (k:=k) (o i) 0; rw [loops_id,sub_zero] at hx
       let l:=separation (E (o i) k) 0; have hr:d= C.S.a k*(K:ℝ):=(C.S.embeds_scale R).symm; have hf: (2:ℝ)*((B:ℝ)^2+4) ≤ K:=by exact_mod_cast ht
       have hz : 2*l + B^2 ≤ K:=by
           apply (Nat.cast_le (α:=ℝ)).mp; push_cast; let a:=C.S.a k; have hy:0<a:= C.S.a_pos k; change a*(l:ℝ)≤a+_ at hx; apply le_of_mul_le_mul_left _ hy; change d=a*K at hr; nlinarith only [hy,hx,mul_le_mul_of_nonneg_left hf hy.le,hr,mul_nonneg hy.le (sq_nonneg (B:ℝ)),(show 8*‖C.S.place (o i)‖≤ d from hc i)]
       unfold l at hz; exact Nat.le_sub_of_add_le hz
   rintro ⟨u,i⟩ ⟨v,l⟩ hu; simp_rw [placeR h]
   let U:= bites C m j p (o i) k (u,true); let Y:=bites C m j p (o l) k (v,true); have h₁:= reachBit C m j p k (o i) h u true; have h₂:= reachBit C m j p k (o l) h v true
   let W:=Mix.camp C p m k; have hf: K ≤ separation (W u) (W v):=by dsimp only [W]; rw [elev C m p k h u, elev C m p k h v,Station.both]; exact Nat.le_mul_of_pos_right _ (separation_pos _ _ hu)
   have hy:=separation_triangle (W u) U Y; have hX:= separation_triangle (W u) Y (W v); rw [separation_comm (W u) U] at hy
   change separation U (W u) ≤ separation (E (o i) k) 0 at h₁; change separation Y (W v) ≤ separation (E (o l) k) 0 at h₂; change B^2 ≤ separation U Y; have h':2*(B^2+4)≤ K:= ht; have hc:=he i; have ht':= he l; omega
end SitePlan
end YM.OPE.Yarn

