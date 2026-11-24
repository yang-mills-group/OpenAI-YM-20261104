import YM.RegulatorIR.Momentum.Block

/-! Differential stencil across MANY roots. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry
open scoped Topology ENNReal NNReal BigOperators Classical
variable {J X Y:Type}{u m r s:ℕ}

def windA (K:Long X→Long Y→ℝ)(p:Cover)(z:Regalia X):Moves Axis → Long Y→ℝ:= fun v=> K (ask (p+v) z)
-- t=D schedule length natural F pre cost (incl tensor label counts but not s).
structure PriceW (K:Long X→Long Y→ℝ)(s u m:ℕ)(F:ℝ≥0∞):Prop where
 cost (p: Cover)(v:Regalia X)(l:List Axis)(h:l.length ≤ m) (x:Moves Axis): quota (journey (windA K p v) l x) (fun i=>quotes (p+x) i s u) ≤ F*award s ^ (1+l.length)

section Employment
-- basis-specific Layer sequences. Product real (can be huge). ∆ gather assigned words.
variable (K:Fin r→Long X→Long Y→ℝ)(p:Cover)(A:Fin r→Regalia X)
def route_up (l:List (Fin r × Axis))(i:Fin r) : List Axis := l.filterMap fun a=>if a.1=i then some a.2 else none
lemma etablished (l:List (Fin r× Axis))(i:Fin r) : (route_up l i).length ≤ l.length:=List.length_filterMap_le ..
lemma rolls_up (l:List (Fin r× Axis)): ∑ i:Fin r,(route_up l i).length=l.length:=by
 induction l with
 | nil=>simp [route_up]
 | cons a l ih=>
    have he (i): (route_up (a::l) i).length=(route_up l i).length+if a.1=i then 1 else 0:=by simp [route_up,List.filterMap_cons]; split_ifs <;> simp
    simp_rw [he,sum_add_distrib]; rw [ih];simp

def mint (K:Fin r→Long X→Long Y→ℝ)(p:Cover)(A:Fin r→ Regalia X)(l:List (Fin r×Axis))(v: MovesR r) (x:Tuple (Long Y) r):ℝ:=∏ i, journey (windA (K i) p (A i)) (route_up l i) (confers v i) (x i)
-- journey order nuance: composition ∆ cons prepend acts first (need append at step)
lemma onward (T:Moves Axis→ Long Y→ℝ)(l:List Axis)(j:Axis): journey T (l++[j])=spring (journey T l) j:=by induction l generalizing T with
 | nil=>rfl
 | cons a l ih=> exact ih _
lemma onward_p (T:MovesR r→ Tuple (Long Y) r→ℝ)(l:List (Fin r × Axis))(j:Fin r × Axis): journey T (l++[j])=spring (journey T l) j:=by induction l generalizing T with
 | nil=>rfl
 | cons a l ih=> exact ih _
lemma flung (v:MovesR r) (i:Fin r) (a: Fin r × Axis) : confers (v+hop a) i= if i=a.1 then confers v i+hop a.2 else confers v i:=by
 rcases a with ⟨j,t⟩; change _=if i=j then _ else _; split_ifs with h
 · ext b; unfold confers;simp only [Pi.add_apply,hops,Prod.mk.injEq,h,true_and]
 ext b; unfold confers;simp only [Pi.add_apply,hops,Prod.mk.injEq,h,false_and,if_false,add_zero]
lemma yields (l:List (Fin r×Axis))(a: Fin r×Axis) : spring (mint K p A l) a=mint K p A (l++[a]):=by
 let f (i:Fin r)(x:Cover):= journey (windA (K i) p (A i)) (route_up l i) x
 ext1 v;ext1 x; let q(i):= f i (confers v i) (x i)
 have he :route_up (l++[a]) a.1=route_up l a.1++[a.2]:= by simp [route_up]
 have hf : ∀ i∈univ.erase a.1,f i (confers (v+hop a) i) (x i)=q i:=by
   intro i hi; rw [flung,if_neg (mem_erase.mp hi).1]
 have hv :∀ i∈univ.erase a.1, journey (windA (K i) p (A i)) (route_up (l++[a]) i) (confers v i) (x i)=q i:=by
   intro i hi; have h: route_up (l++[a]) i=route_up l i:= by simp [route_up, Ne.symm (mem_erase.mp hi).1]
   rw [h]
 change (∏ i,f i (confers (v+hop a) i) (x i))-(∏ i:Fin r,q i)= _; unfold mint
 rw [← mul_prod_erase _ _ (mem_univ a.1),← mul_prod_erase _ q (mem_univ a.1), ← mul_prod_erase _ (fun i=> journey (windA (K i) _ _) (route_up (l++[a]) i) _ _) (mem_univ a.1), prod_congr rfl hf, prod_congr rfl hv, ← sub_mul,he,onward,flung, if_pos rfl]; rfl
lemma montage (l:List (Fin r×Axis)): journey (mint K p A []) l=mint K p A l:=by
 induction l using List.reverseRecOn with
 | nil=>rfl
 | append_singleton l a ih=> rw [onward_p,ih,yields]

variable {F:ℝ≥0∞}(H:∀ i,PriceW (K i) s u m F)(hs:0<s)
include H
lemma itinerary (l:List (Fin r × Axis))(v:MovesR r)(h:l.length ≤ m) : quota (mint K p A l v) (wall p s u) ≤ (F*award s)^r * (1+award s*extent v)^u * (award s)^l.length:=by
 apply le_trans (quota_mono _ (wages (u:=u) (s:=s) v p))
 rw [show (fun x:Tuple (Long Y) r=> (1+_ :ℝ≥0∞)^u*∏ i, _ )= (fun x=> (∏ i,quotes (p+confers v i) (x i) s u) * (1+award s * extent v)^u) from funext fun i=> mul_comm ..,quota_raised, mul_right_comm _ _ ((award s)^l.length)]; unfold mint; rw [produced r (fun i=> journey (windA (K i) p (A i)) (route_up l i) (confers v i)) (fun i x=> quotes (p+confers v i) x s u)]
 apply mul_le_mul_left; apply le_trans (Finset.prod_le_prod' (fun i _=>(H i).cost _ _ _ ((etablished l i).trans h) _))
 simp_rw [pow_add,pow_one, ← mul_assoc F,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
 rw [prod_pow_eq_pow_sum,rolls_up,← mul_pow]

include hs
lemma itinerary_forms : Controls (mint K p A []) (wall p s u) (s:ℝ≥0∞) ((F*award s)^r*2^u) u m:=by
 refine ⟨(by exact_mod_cast hs),by finiteness,?_,?_⟩
 · intro i hi l hl v h; rw [montage,← hl]; apply (itinerary K p A H l v (hl.trans_le hi)).trans
   apply mul_le_mul_left;apply mul_le_mul_right; have ht:award s * (s:ℝ≥0∞)=1:=ENNReal.inv_mul_cancel (by exact_mod_cast hs.ne') (by finiteness)
   apply pow_le_pow_left'; apply le_trans (add_le_add_right (mul_le_mul_right h (award s)) (1:ℝ≥0∞)); rw [ht];norm_num
 intro v
 have hp:= itinerary K p A H [] v (by simp)
 rw [List.length_nil,pow_zero,mul_one] at hp; exact hp.trans (mul_le_mul_left (le_mul_of_one_le_right bot_le (one_le_pow₀ (by norm_num))) _)
end Employment
end YM.RegulatorIR.Momentum
