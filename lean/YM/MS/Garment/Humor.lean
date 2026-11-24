import YM.MS.Garment.Seam
import YangMills.WilsonProof.NativeSupport.YM.MS.KoszulIndex
/-!
# Color/sym/ghost and grade rotation

Rank step performed at all. Master consistency needs parity as Property. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{b c: Bool}{m n:ℕ}{U:Rip G}{F H:Mob G}
-- row sym and channel
abbrev hair (v:Legs (Shore G m)) : ℤ:= fieldDim ghostNo v
def Ghost (t:ℤ)(F:Mob G): Prop:= ∀ m, Rails (ghostNo ∘ Prod.fst) t (F m)
def Credit (b:ℤ)(U:Rip G): Prop:= ∀ m i j p,U m i j p≠0 → ghostNo i+ghostNo j= -b
lemma hair_ext (h:m≤n) (l:Legs (Shore G m)): hair (Arts.lift h l)=hair l:= by induction l with| nil=>rfl| cons i l ih=> rw [show Arts.lift h (i::l)=(embA (rises h) i.1,Left h i.2)::Arts.lift h l from rfl, hair, field_cons, show fieldDim ghostNo (Arts.lift h l)=_ from ih]; unfold hair; rw [field_cons] ; rcases i with ⟨⟨⟨_|a,_|_⟩,c⟩,p⟩ <;> rfl
lemma railZero (h:Ghost 0 F): tide F:= by
    intro m; refine Rails.parity (hF:=h m) ?_; intro i; rcases i with ⟨⟨⟨_|a,_|_⟩,c⟩,b⟩ <;> rfl
lemma sym_tree (h:Rock.sym F)(hh:Rock.sym H)(he:closedF U b): Rock.sym (arbor U F H):= fun m=> tree_sym (he m) (h m) (hh m)
lemma sym_trc' (h:Rock.sym F)(m:ℕ)(p): Symm (field Landau.parity) (trc (U m) p (F m)):= by
    classical
    simpa [slab] using slab_sym (K:=U m) ({p}:Finset _) (h m)
lemma hair_split {u v w:Legs (Shore G m)}(h:Split u v w): hair u+hair v=hair w:= split_sum _ h
lemma sym_lift (h:m≤n){F:Rack G n}(hx:Symm (field Landau.parity) F): Symm (field Landau.parity) (pulls h F):= by
   intro l i j k; unfold pulls Arts.lift; simp only [List.map_append,List.map_cons]; rw [hx]; unfold field; simp [risesP] -- auth.
lemma sym_strand {s:ℂ}(h:Rock.sym F)(hf:Form0 b F)(hr:Knot b U)(hx:s∈Town): Rock.sym (ocean s U F):= by
   have hu m (x:SectorP m): Symm (field Landau.parity) (Wtr s U F x):= by
       rw [combo s m]; have hh (M:ℕ)(he:m≤M): Symm (field Landau.parity) (Wtr M U F x):= by rw [funext (fun l=>tallyN (x:=x) (l:=l) hf.token hr.token he)]; exact sym_lift he (sym_trc' h M (Left he x)); -- syntax
       exact (hh m (le_refl _)).add (((hh (m+1) (by omega)).sub (hh m (le_refl _))).smul _)
   intro m l i j k; apply sub_eq_zero.mp; -- remove f stuck
   exact Garment.erase hr hf hx (L:=fun F:Rack G m=>F (l++i::j::k)-cross (Landau.parity i.1) (Landau.parity j.1)* F (l++j::i::k)) ( (Centre _).sub_mem (centroid _) (cent_scale _ _ (centroid _))) (fun p=> sub_eq_zero.mpr (sym_lift _ (hu _ p) l i j k))
lemma Occup {i j k:ℤ}(h:Ghost i F)(hh:Ghost j H)(he:Credit k U)(hr:reverseF U) : Ghost (i+j+k) (arbor U F H):= by
   intro m l hv; change hair l ≠ _ at hv; unfold arbor tree; rw [scatter_congr _ _ _ (fun _ _=>(0:ℂ)) ?_]; exact map_zero (allocate ..)
   intro a b hp; rw [convertR (hr m)]; refine Finset.sum_eq_zero (fun s _=> Finset.sum_eq_zero fun t _=> ?_ ); unfold radius; dsimp only
   by_cases hx : U m s t (-net a)=0; simp [hx]; obtain ht:= he m s t (-net a) hx; obtain hhx:= hair_split hp; by_cases hF : hair ((s,-net a)::a)=i; swap; · rw [h m _ hF]; simp
   rw [hh m _ (show hair ((t,- -net a)::b) ≠ _ from ?_),mul_zero]; rw [hair,field_cons] at hF ⊢; dsimp only at hF ⊢; unfold hair at *; omega
lemma charge_pose {i j:ℤ}(h:Ghost i F)(hc:Credit j U)(p:SectorP m)(w:Legs (Shore G m))(hm: hair w ≠ i+j): trc (U m) p (F m) w=0:= by
    rw [at_trc]; refine Finset.sum_eq_zero (fun a _=> Finset.sum_eq_zero fun b _=>?_); by_cases he:U m a b p=0; rw [he,zero_mul]; obtain hp:=hc m a b p he; rw [h m _ (show hair ((a,_)::(b,_)::w) ≠i from ?_), mul_zero]; simp only [hair,field_cons]; unfold hair at hm; omega
lemma ghost_l (i j:ℤ)(h:Ghost i F)(hc:Credit j U)(hf:Form0 b F)(hr:Knot b U){s:ℂ}(hx:s∈Town): Ghost (i+j) (ocean s U F):= by
    intro m l hl; change hair l ≠ _ at hl; refine Garment.erase hr hf hx (centroid l) (fun p=>?_); let M:= m+1; change Wtr s _ _ p _=0; rw [combo s M,Pi.add_apply,Pi.smul_apply,Pi.sub_apply]; simp_rw [tallyN hf.token hr.token (le_refl M), tallyN hf.token hr.token (Nat.le_succ M)]; have he {n}(h:m+1≤n): hair (Arts.lift (G:=G) h (Arts.lift (Nat.le_succ m) l))≠ i+j:= by rw [hair_ext,hair_ext]; exact hl
    rw [charge_pose h hc (Left _ p) _ (he _), charge_pose h hc (Left _ p) _ (he _), sub_self]; simp
lemma plow_sym (h:Rock.sym F)(b:ℂ)(t:ℝ): Rock.sym (plow b t F):= by intro m l i j k; unfold plow; have hz:=h m (sr t l); simp only [Price_append,Price_cons,sr,List.map_append,List.map_cons]; rw [add_left_comm (wfield i.1), h m]; dsimp only [field]; ring
lemma plow_ghost {i:ℤ}(h:Ghost i F)(c:ℂ)(t:ℝ): Ghost i (plow c t F):= by
    have hx (m:ℕ)(l:Legs (Shore G m)): chargeInt (ghostNo ∘ Prod.fst) (sr t l)= chargeInt (ghostNo ∘ Prod.fst) l:= by induction l with| nil=>rfl| cons i l ih=> unfold sr at *; simp only [List.map_cons,charge_int,ih]; rfl
    intro m l he; unfold plow; apply mul_eq_zero_of_right; apply h m; rw [hx]; exact he
end YM.MS.Garment
