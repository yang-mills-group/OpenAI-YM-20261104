import YM.OPE.Loom.Budget
/-! Helpers for last-step assembly geometry keeping every copy separated through
observation and afterwards. Adapted from MultipleContact/Bunch/Arrangement.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker YM.Next.Rank.Station YM.Extra.Multi YM.Next.Rank
variable {G:Gauge} {C:Family G}{n:Side}{m k j p i :ℕ}{x : Site (C.side j p)} {v : ℝ} {α: Type}[Fintype α][DecidableEq α]
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "P" => C.path.levels.budget
local notation "S" => C.S
local notation "W" => Site (C.side m p)
set_option quotPrecheck false
lemma upper (x:Site (C.side j p)) (hk:k≤j) {d : ℕ} (hh:‖C.S.place x‖ ≤ C.S.a k*d) : separation (loops C j p x k) 0 ≤ d+1:=by
    let Z:= C.S.toDepth hk p; let B:= separation (loops C j p x k) 0; let c:= Z.count.val; let y:= C.S.place x
    have hV: 2*separation x (Z.embed (loops C j p x k))< c:= (by rw [vote C _ _ _ _ hk]; exact Station.midway _ (C.S.toDepth_odd hk p) _)
    have hz : separation (Z.embed (loops C j p x k)) 0 = c*B:=by nth_rw 1 [show (0:Site (C.side j p))=Z.embed 0 from Z.root.map_zero.symm]; exact Station.both ..
    have hq:= separation_triangle (Z.embed (loops C j p x k)) x 0; rw [separation_comm (Z.embed _) x,hz] at hq
    have hy : C.S.a j*c=C.S.a k:= C.S.embeds_scale Z; have ha₀:= C.S.a_pos j; have hp':= C.S.a_pos k
    obtain ⟨h₁,-⟩:= normC C j p x
    have hR: C.S.a k*(B:ℝ) ≤ C.S.a k+‖y‖:= by
       rw [← hy,mul_assoc]; have hx: ((c*B:ℕ):ℝ)≤ c+(separation x 0:ℝ):= by exact_mod_cast (show c*B≤ c+separation x 0 by omega)
       rw [Nat.cast_mul] at hx; exact (mul_le_mul_of_nonneg_left hx ha₀.le).trans (by rw [mul_add]; linarith only [h₁])
    have ht : (B:ℝ) ≤ (d:ℝ)+1:= by apply le_of_mul_le_mul_left (a:=C.S.a k) _ hp'; linarith only [hh,hR]
    exact_mod_cast ht
lemma separation_alt {n:Side}(x y: Site n): separation x y=separation (x-y) 0:=by rw [← separation_translate x y (-y)]; simp [sub_eq_add_neg]
lemma lower {x y:Site (C.side j p)} (hk:k≤j) {d : ℕ}(hp: (2*C.S.a k)*(d+1:ℝ)≤ ‖C.S.place (x-y)‖) : d ≤ separation (loops C j p x k) (loops C j p y k):=by
    obtain ⟨-,h₂⟩:= normC C j p (x-y)
    let Z:= C.S.toDepth hk p; let B:= separation (loops C j p x k) (loops C j p y k); let n:= Z.count.val
    have hV i: 2*separation i (Z.embed (loops C j p i k))< n:= (by rw [vote C _ _ _ _ hk]; exact Station.midway _ (C.S.toDepth_odd hk p) _)
    have hz : separation (Z.embed (loops C j p x k)) (Z.embed (loops C j p y k)) = n*B:= Station.both ..
    have hM: separation (x-y) 0 ≤ B*n+n:=by
        have hL:= separation_triangle x (Z.embed (loops C j p x k)) (Z.embed (loops C j p y k))
        have hR:= separation_triangle x (Z.embed (loops C j p y k)) y; rw [hz] at hL; rw [separation_comm (Z.embed _) y] at hR
        rw [← separation_alt,mul_comm B]; have hN:= hV x; have hC:=hV y; omega
    have hy : C.S.a j*n=C.S.a k:= C.S.embeds_scale Z; have ha:= C.S.a_pos j; have hp':= C.S.a_pos k
    have hs: C.S.a j*(separation (x-y) 0:ℝ) ≤ C.S.a k*(B+1:ℝ):=by
         rw [← hy]; refine (mul_le_mul_of_nonneg_left (show (separation (x-y) 0:ℝ)≤ ((B*n+n:ℕ):ℝ) from (by exact_mod_cast hM)) ha.le).trans_eq (by push_cast; ring)
    have ht: (d:ℝ) ≤ B:=by nlinarith only [hp,h₂,hs,hp']
    exact_mod_cast ht
lemma at_point (v:W) : bites C m j p 0 k (v,true)=Mix.camp C p m k v:=by
   have h: loops C j p 0 k=0:=by
      unfold loops; split
      next he=> exact (C.S.toDepth he p).root.map_zero
      next he=> have hk' : (C.S.toDepth (Nat.le_of_lt (Nat.lt_of_not_ge he)) p).root 0=0:= (C.S.toDepth _ p).root.map_zero
                exact hk' ▸ (Ratio.embed_parent _ _)
   simp [bites,h,affine]
local notation "E"=>Mix.camp C p m k
lemma across {u d:ℕ} (hm : m≤k)(x y:Site (C.side j p)) (hx:separation (loops C j p x k) 0≤u)(hy:separation (loops C j p y k) 0≤u)(hp:d+2*u≤(C.S.toDepth hm p).count.val)(a b:W)(h:a≠b): d≤ separation (bites C m j p x k (a,true)) (bites C m j p y k (b,true)):= by
   have ht:(C.S.toDepth hm p).count.val ≤ separation (E a) (E b):=by simp_rw [elev C m p k hm,Station.both]; exact Nat.le_mul_of_pos_right _ (separation_pos _ _ h)
   let c:= bites C m j p x k (a,true); let d:=bites C m j p y k (b,true); have hz:= (reachBit C m j p k x hm a true).trans hx; have he:= (reachBit C m j p k y hm b true).trans hy; have hh:=separation_triangle (E a) c d; have hf:=separation_triangle (E a) d (E b); rw [separation_comm (E a) c] at hh; unfold c d at *; omega
omit [DecidableEq α] in
lemma bucket {n:Side}{o:W×α→Site n}{r b:ℕ} (hb:0<b)(hf: Fintype.card α≤r)(hx: Cross b o): Occupancy o r:= by
   intro y; apply le_trans _ hf; rw [← Finset.card_univ]; refine Finset.card_le_card_of_injOn Prod.snd (fun _ _=> Finset.mem_univ _) ?_
   intro x mx q mq h; rw [SetLike.mem_coe] at mx mq
   have ht : o x = o q:= (Finset.mem_filter.mp mx).2.trans (Finset.mem_filter.mp mq).2.symm
   refine Prod.ext ?_ h; by_contra hi; have he:= hx x q hi; rw [ht,separation_self] at he; exact Nat.not_lt_of_le he (pow_pos hb _)
end YM.OPE.Loom
