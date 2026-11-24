import YM.RegulatorIR.Budget.Ray

/-! When the connecting line has already been pulled on one piece, binary
heat connectivity just uses pointwise sharing. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Set Tuple Layer Motion Packet
open scoped ENNReal NNReal Topology BigOperators Classical
variable {r s:ℕ} {X Y : Type} {P:ℝ}
namespace Tuple
variable (u:Tuple X r)(v:Tuple X s)(x:X)(A:Tariff X)
lemma diameter_swap : A.diameter (Fin.append u v)=A.diameter (Fin.append v u):= by
 have H {r s:ℕ}(u:Tuple X r)(v:Tuple X s) : A.diameter (Fin.append u v) ≤ A.diameter (Fin.append v u):=by
    apply A.diameter_le (A.diameter_unit _); intro p q
    induction p using Fin.addCases <;> induction q using Fin.addCases <;> rename_i i j
    · have H:= A.diameter_ge (Fin.append v u) (Fin.natAdd s i) (Fin.natAdd s j);simpa using H
    · simpa using A.diameter_ge (Fin.append v u) (Fin.natAdd s i) (Fin.castAdd r j)
    · simpa using A.diameter_ge (Fin.append v u) (Fin.castAdd r i) (Fin.natAdd s j)
    simpa using A.diameter_ge (Fin.append v u) (Fin.castAdd r i) (Fin.castAdd r j)
 exact le_antisymm (H ..) (H ..)
lemma shared_diam : A.diameter (Fin.append u v) ≤ A.diameter (Fin.cons x u)*A.diameter (Fin.cons x v):=by
 let U:= A.diameter (Fin.cons x u); let V:=A.diameter (Fin.cons x v)
 have h (i j): A.road (u i) x≤U ∧ A.road x (v j)≤ V:=by
    constructor
    · simpa [U] using A.diameter_ge (Fin.cons x u) (Fin.succ i) 0
    simpa [V] using A.diameter_ge (Fin.cons x v) 0 (Fin.succ j)
 apply A.diameter_le (one_le_mul (A.diameter_unit _) (A.diameter_unit _)); intro p q
 induction p using Fin.addCases <;> induction q using Fin.addCases <;> rename_i i j
 · apply le_trans ?_ (by nth_rw 1 [← mul_one U];exact mul_le_mul_right (A.diameter_unit (Fin.cons x v)) U : U≤U*V)
   simpa [U] using A.diameter_ge (Fin.cons x u) i.succ j.succ
 · simp only [Fin.append_left,Fin.append_right];exact (A.tri (u i) x (v j)).trans (mul_le_mul' (h i j).1 (h i j).2)
 · simp only [Fin.append_left,Fin.append_right]; rw [A.symm];exact (A.tri (u j) x (v i)).trans (mul_le_mul' (h j i).1 (h j i).2)
 apply le_trans ?_ (by nth_rw 1 [← one_mul V];exact mul_le_mul_left (A.diameter_unit (Fin.cons x u)) V : V≤U*V)
 simpa [V] using A.diameter_ge (Fin.cons x v) i.succ j.succ
lemma shared_mark (B:Premium A) : B.width (Fin.append u v) ≤ B.width (Fin.cons x u)*A.diameter (Fin.cons x v):= by
 apply B.width_le ((shared_diam ..).trans (mul_le_mul_left (B.width_diameter _) _)); intro p; induction p using Fin.addCases <;> rename_i i
 · rw [Fin.append_left]; have he:= B.width_ge (Fin.cons x u) i.succ; rw [Fin.cons_succ] at he
   exact (mul_one _).ge.trans (mul_le_mul' he (A.diameter_unit _))
 rw [Fin.append_right]; have he:= B.width_ge (Fin.cons x u) 0; rw [Fin.cons_zero] at he
 apply (B.travel (v i) x).trans; apply mul_le_mul' he; simpa using A.diameter_ge (Fin.cons x v) i.succ 0

def overL (i:Fin r)(x:X): (Hold i x × Tuple X s) ≃ Hold (Fin.castAdd s i) x where
 toFun p:= ⟨Fin.append p.1.val p.2,(Fin.append_left ..).trans p.1.property⟩
 invFun p:= (⟨cutLeft p.val,p.property⟩, cutRight p.val)
 left_inv p:= by apply Prod.ext; apply Subtype.ext; apply cutleft; apply cutright
 right_inv p:= Subtype.ext (Tuple.recombine p.val)
def overR (i:Fin s)(x:X): (Tuple X r × Hold i x) ≃ Hold (Fin.natAdd r i) x where
 toFun p:= ⟨Fin.append p.1 p.2.val,(Fin.append_right ..).trans p.2.property⟩
 invFun p:=(cutLeft p.val,⟨cutRight p.val,p.property⟩)
 left_inv _:= Prod.ext (cutleft ..) (Subtype.ext (cutright ..))
 right_inv p:= Subtype.ext (Tuple.recombine p.val)
def underL (i:Fin r)(x:X): X × Hold i x≃ Hold i.succ x where
 toFun p:=⟨Fin.cons p.1 p.2.val,by change Fin.cons (α:=fun _=>X) p.1 p.2.val i.succ=x;rw [Fin.cons_succ]; exact p.2.property⟩
 invFun p:=(p.val 0,⟨Fin.tail p.val,p.property⟩)
 left_inv p:= by
    change (Fin.cons (α:=fun _=>X) p.1 p.2.val 0, _) = p
    ext1
    · rfl
    apply Subtype.ext; exact Fin.tail_cons (α:=fun _=>X) p.1 p.2.val
 right_inv p:=Subtype.ext (Fin.cons_self_tail ..)
def still (x:X): Tuple X s ≃ Hold (0:Fin (s+1)) x where
 toFun v:=⟨Fin.cons x v,rfl⟩
 invFun v:=Fin.tail v.val
 left_inv _:= Fin.tail_cons ..
 right_inv v:= Subtype.ext <| (congr_arg (fun y:X=> (Fin.cons y (Fin.tail v.val):Tuple X (s+1))) (show x=v.val 0 from v.property.symm)).trans (Fin.cons_self_tail ..)
end Tuple

namespace Packet
variable (T:Packet X (r+1))(U:Packet X (s+1)) {A:Tariff X} {c d:ℝ≥0∞}
def lace (p:Tuple X r) (q:Tuple X s) (x) := T (Fin.cons x p)* U (Fin.cons x q)
def splice (z: Tuple X (r+s)) := ∑' x, lace T U (cutLeft z) (cutRight z) x
lemma splice_at (p: Tuple X r)(q:Tuple X s): splice T U (Fin.append p q)=∑' x,lace T U p q x:=by simp_rw [splice, cutleft,cutright]
lemma twist (p:Tuple X r)(q:Tuple X s) : splice T U (Fin.append p q)=splice U T (Fin.append q p):=by rw [splice_at,splice_at]; exact tsum_congr fun _=> mul_comm ..
lemma lace_span {B:Premium A}(p:Tuple X r)(x)(h:localQ A U d):
    quota (fun q:Tuple X s=>lace T U p q x) (fun q=> B.width (Fin.append p q)) ≤ (‖T (Fin.cons x p)‖ₑ*B.width (Fin.cons x p))*d :=by
 refine le_trans ?_ (mul_le_mul_right (h (0:Fin (s+1)) x) _)
 unfold Stalk.scopeQ quota; rw [← (still (s:=s) x).tsum_eq, ← ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum; intro v
 change ‖lace T U p v x‖ₑ*_ ≤ _* (‖U (Fin.cons x v)‖ₑ*_)
 rw [lace, enorm_mul]; exact le_trans (mul_le_mul_right (shared_mark ..) _) (mul_mul_mul_comm ..).le
lemma splice_holder (h:localQ A U d)(p:Tuple X r)(x):
  quota (fun q:Tuple X s=>lace T U p q x) (fun q=>A.diameter (Fin.append p q))≤ (‖T (Fin.cons x p)‖ₑ*A.diameter (Fin.cons x p))*d :=by
  simpa only [Premium.free_cost] using lace_span T U (B:=Premium.free A) p x h
lemma splice_first (ht:localQ A T c)(hu:localQ A U d)(x:X)(i:Fin r):
   quota (fun z:Hold i x × X × Tuple X s=>lace T U z.1.val z.2.2 z.2.1)
      (fun p=> A.diameter (Fin.append p.1.val p.2.2)) ≤ c*d := by
 refine le_trans ?_ (mul_le_mul_left (ht i.succ x) _)
 unfold quota Stalk.scopeQ; unfold quota
 rw [← (underL i x).tsum_eq,ENNReal.tsum_prod']
 change _ ≤ (∑' p:X×Hold i x,‖T (Fin.cons p.1 p.2.val)‖ₑ*A.diameter (Fin.cons p.1 p.2.val))*d
 rw [ENNReal.tsum_prod (f:=fun y (a:Hold i x)=> ‖T (Fin.cons y a.val)‖ₑ*A.diameter (Fin.cons y a.val)),
    ENNReal.tsum_comm (f:=fun y (a:Hold i x)=> ‖T (Fin.cons y a.val)‖ₑ*A.diameter (Fin.cons y a.val)), ← ENNReal.tsum_mul_right]
 refine ENNReal.tsum_le_tsum (fun a=>?_)
 rw [ENNReal.tsum_prod',← ENNReal.tsum_mul_right]; exact ENNReal.tsum_le_tsum fun y=> splice_holder T U hu a.val y
lemma splice_left (ht:localQ A T c)(hu:localQ A U d)(i:Fin r)(x:X): Stalk.scopeQ (fun z:Tuple X (r+s)=>z (Fin.castAdd s i)) (splice T U) A.diameter x≤c*d:=by
 unfold Stalk.scopeQ
 rw [← quota_perm (overL i x)]
 change quota (fun z: Hold i x × Tuple X s=>splice T U (Fin.append z.1.val z.2)) _ ≤ _
 simp_rw [splice_at]
 refine (inside_quota (fun (v:Hold i x×Tuple X s) y=>lace T U v.1.val v.2 y) _).trans ?_
 unfold quota; rw [ENNReal.tsum_prod']
 have H:= splice_first T U ht hu x i; unfold quota at H; rw [ENNReal.tsum_prod'] at H; apply le_trans _ H; apply ENNReal.tsum_le_tsum;intro a; rw [ENNReal.tsum_prod']; exact ENNReal.tsum_comm (f:=fun v y=>‖lace T U a.val v y‖ₑ*A.diameter (Fin.append a.val v)) |>.le
lemma splice_local (ht:localQ A T c)(hu:localQ A U d) : localQ A (splice T U) (c*d):=by
 intro j x; induction j using Fin.addCases <;> rename_i i
 · exact splice_left T U ht hu i x
 unfold Stalk.scopeQ
 rw [← quota_perm (overR i x)]
 have hh := splice_left U T hu ht i x
 unfold Stalk.scopeQ at hh; rw [← quota_perm (overL i x),mul_comm] at hh
 unfold quota at hh ⊢; rw [← (Equiv.prodComm _ _).tsum_eq]; apply le_trans ?_ hh; apply ENNReal.tsum_le_tsum; intro w
 change ‖splice T U (Fin.append w.2 w.1.val)‖ₑ*A.diameter (Fin.append w.2 w.1.val)≤ _
 rw [twist,diameter_swap]; exact le_rfl
lemma splice_mark {B:Premium A}(h:localQ A U d): markQ B (splice T U) ≤ markQ B T*d:= by
 unfold markQ; rw [← quota_perm (Fin.appendEquiv ..)]
 change quota (fun p:Tuple X r × Tuple X s=>splice T U (Fin.append p.1 p.2)) _ ≤ _
 simp_rw [splice_at]; apply (inside_quota (fun (p:Tuple X r × Tuple X s) x=>lace T U p.1 p.2 x) _).trans
 unfold quota; rw [← (Tuple.glueEquiv X r).tsum_eq,ENNReal.tsum_prod']
 change _≤ (∑' p:X×Tuple X r,‖T (Fin.cons p.1 p.2)‖ₑ * B.width (Fin.cons p.1 p.2))*d
 rw [ENNReal.tsum_prod (f:=fun x v=>‖T (Fin.cons x v)‖ₑ*B.width (Fin.cons x v)), ENNReal.tsum_comm (f:=fun x v=>‖T (Fin.cons x v)‖ₑ*B.width (Fin.cons x v)),← ENNReal.tsum_mul_right]
 apply ENNReal.tsum_le_tsum;intro a; rw [← ENNReal.tsum_mul_right]
 exact ENNReal.tsum_comm (f:=fun (v:Tuple X s) y=>‖lace T U a v y‖ₑ*B.width (Fin.append a v))|>.le.trans (ENNReal.tsum_le_tsum fun x=> lace_span T U a x h)
end Packet
end YM.RegulatorIR.Budget
