import YM.FormalBulk08.Aster.Peel

/-! Reset formula express without last bookkeeping cost in repeated
component. Readout known invariant affine-null. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Lattice Laurent Bloch Exterior RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge}{X:Type}{r e E:ℕ} (a:hue G) (W:Pot G) (S:Slopes G) {τ:Time X} {σ η δ A B C D:X→ℝ}
-- always use same color (lemma independent)

def nickel (e j r:ℕ) := Wine.bill (bookH (Wine.scalar a W)) (bookU (Wine.scalar a W)) e j r
def penny (e r:ℕ) : Tile (edgeL G) r:= ∑ j ∈(Finset.range e).erase 0,nickel a W e j r • W j r
def limiter (T:Tile (edgeL G) r) :Tile (edgeL G) r:= T - if h:r=2 then value a (lengthen h T) • lengthen h.symm S else 0
lemma plus_purse {T K:Slopes G}(h:Purse T)(p:Purse K): Purse (T+K):= by
    obtain ⟨σ,C,c,A⟩:=h; obtain ⟨η,B,e,H⟩:=p; exact ⟨min σ η,_, lt_min c e,(A.shrink (min_le_left ..)).add (H.shrink (min_le_right ..))⟩
lemma joining {j:ℕ}{V:Train j}{k:ℝ}(h:Story W (pink k V))(hx:0<k)(ht:4≤j)(he:0<e)(r): Wine.normalized a W e r = limiter a (W 0 2) (W e r + penny a W e r):= by
    have hp r: nickel a W e e r=1:=by rw [nickel,Wine.bill, Nat.sub_self];exact ((book_fresh _).pow _).mul ((book_guard _).pow _)
    have hh r : Wine.normalized a W e r=(W e r + penny a W e r)+ nickel a W e 0 r • W 0 r:= by
       change (∑ j∈Finset.range (e+1), nickel a W e j r • W j r) = _; rw [Finset.sum_range_succ, hp r, one_smul,← Finset.add_sum_erase (Finset.range e) _ (Finset.mem_range.mpr he)]; unfold penny;abel
    by_cases ha:r=2
    · subst r;obtain ⟨hh',hv⟩:=rulecraft a W h hx ht
      have H:value a (Wine.normalized a W e 2)=0:= by have h:=congr_arg (coeff e) hv;rwa [scalar,coeff_mk,coeff_one,if_neg (Nat.ne_of_gt he)] at h
      let T:= W e 2 + penny a W e 2
      have hu j:Purse (nickel a W e j 2 • W j 2):= by obtain ⟨s,B,b,H⟩:=h.fare j 2; exact ⟨s,_,b,H.smul _⟩
      have hz: value a T + nickel a W e 0 2=0:= by
           have hr: Purse (penny a W e 2):=(income_sum a _ _ (fun i _=> hu i)).1
           rw [hh,value_add (plus_purse (h.fare _ _) hr) (hu 0), value_coin, (show value a (W 0 2)=1 by rw [h.ink,pink_weigh k hx ht]), mul_one] at H; exact H
      rw [hh]; change T+ _ = T - value a T • W 0 2; rw [show nickel a W e 0 2= -value a T by linarith only [hz], neg_smul,sub_eq_add_neg]
    rw [limiter,dif_neg ha, sub_zero,hh]
    have hh' : W 0 r=0:= by by_contra hp; have hx:=h.valence _ _ hp;omega
    rw [hh',smul_zero,add_zero]
-- pre-block head price duplicated across all ranks
structure Teller (G:Gauge) (σ K:ℝ) :Prop where
   plus : 0≤K
   pump : ∀ i (T:Slopes G) (A:ℝ), Bail (fame _) σ T A→ |value i T| ≤ A*K
lemma teller_made (G:Gauge){σ:ℝ}(hs:0<σ):∃ K:ℝ,Teller G σ K:=by obtain ⟨C,c,h⟩:= priced_hook (G:=G) hs; exact ⟨C,c.le,fun i t a P=>h a t P i⟩
lemma caps_cost (hp:Soft τ A)(hf:∀ i,Teller G (σ i) (A i)){S:X→Slopes G}(H:Cost τ (fun _=> fame _) σ S): Soft τ (fun i=> value a (S i)):= by obtain ⟨C,c,W⟩:= H; exact (c.times hp).below fun x=>((hf x).pump a (S x) (C x) (W x)).trans (le_abs_self _)
lemma teller_pay (hp:Soft τ A)(hf:∀ i,Teller G (σ i) (A i))(h0:∀ i,0<σ i){S T:X→Slopes G}(H:Totem τ (fun _=>fame _) σ δ S T): Pact τ δ (fun i=>value a (S i)) (fun i=> value a (T i)):= by
    obtain ⟨C,c,hK,h⟩:= H.nebula; obtain ⟨B,b,w⟩:= H.left; obtain ⟨D,d,Z⟩:= H.right; refine ⟨caps_cost a hp hf H.left,caps_cost a hp hf H.right,_, c.times hp, fun i=> mul_nonneg (hK i) (hf i).plus,fun i=>?_⟩; rw [Pi.sub_apply,←value_less ⟨_,_,h0 i,w i⟩ ⟨_,_,h0 i,Z i⟩, mul_right_comm]; exact (hf i).pump a _ _ (h i)
lemma limits (T:Tile (edgeL G) r){σ C A B:ℝ}(h:Teller G σ C) (hV:Bail (fame _) σ S A)(ht:Bail (fame _) σ T B): Bail (fame _) σ (limiter a S T) ((1+C*A)*B) := by
    unfold limiter; split
    · rename_i H; subst r; apply (ht.sub (hV.smul (value a T))).mono; refine le_trans (b:=B+B*C*A) (add_le_add_right (α:=ℝ) ?_ B) ?_ -- convention
      · exact mul_le_mul_of_nonneg_right (h.pump a T B ht) hV.1
      exact le_of_eq (by ring)
    rw [sub_zero]; apply ht.mono; nth_rw 1 [←one_mul B]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg h.plus hV.1)) ht.1
lemma limiter_shift {σ C D:ℝ}{T U:Tile (edgeL G) r}(hp:Bail (fame _) σ T C)(he:Bail (fame _) σ U D)(h:0<σ) : limiter a S T-limiter a S U=limiter a S (T-U) := by
    by_cases hx:r=2
    · subst r; change (T - value a T • S) - (U- value a U • S)= _ - value a (T-U) • S; rw [value_less ⟨_,_,h,hp⟩ ⟨_,_,h,he⟩,sub_smul];abel
    simp only [limiter,hx,↓reduceDIte,sub_zero]
lemma limiter_diff (hp:Soft τ A)(hf:∀ i,Teller G (σ i) (A i)){T U: X→Slopes G}{W:X→Tile (edgeL G) r}(h:Dust τ (fun _=> fame _) σ δ (fun i=> T i-U i))(H:Cost τ (fun _=> fame _) σ W): Dust τ (fun _=> fame _) σ δ (fun i=> limiter a (T i) (W i)-limiter a (U i) (W i)) := by
    by_cases hx:r=2
    · subst r; convert ((h.amp (caps_cost a hp hf H)).reverse) using 1; ext1 i; change _-_ -( _-_) = -(value a (W i) • (T i-U i)); change W i - value a (W i) • T i - (W i - value a (W i) • U i)= _ ; rw [smul_sub];abel
    simp only [limiter,hx,↓reduceDIte,sub_zero,sub_self];apply dust_void
end YM.FormalBulk08.Aster
