import YM.MS.Class.ClassThree
/-!
# Off rank range the class vanishes (excluding volume vacuum at rank zero)
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Mark
open scoped Topology ContDiff InnerProductSpace
open Complex (I)
variable {G: Gauge} {F : Law G} {h:ℤ}
lemma nat_cost (w : Lane4 G) : 1≤ wfield w.1:= by unfold wfield dim; cases w.1.1.2 <;> simp
lemma length_pay (w : List (Lane4 G)): (w.length:ℤ)≤fieldDim wfield w:= by
   induction w with
   | nil=> rfl
   | cons a w ih=> have h:= nat_cost a; rw [List.length_cons,Nat.cast_add,field_cons]; omega
lemma pay_eq (w : List (Lane4 G)) (h : (w.length:ℤ)=fieldDim wfield w) : ∀ i∈w,wfield i.1=1:= by
   induction w with
   | nil=> simp
   | cons i w ih=> have hv:=length_pay w; have hp:=nat_cost i; rw [List.length_cons,Nat.cast_add,field_cons] at h; rw [List.forall_mem_cons]; exact ⟨by omega, ih (by omega)⟩ -- rhs pair? 
lemma role_no (i : Lane4 G) (he:wfield i.1=1) : 0 ≤ ghostNo i.1:= by
    rcases i with ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> norm_num [wfield,dim] at he <;> norm_num [ghostNo,ghostChannel]
lemma no_eq (w : List (Lane4 G)) (hx : ∀ i∈w,wfield i.1=1) (h : fieldDim ghostNo w=0) : ∀ i∈w, ghostNo i.1=0:= by
    have hl (v : List (Lane4 G)) (hL : ∀ i∈v,wfield i.1=1) : 0≤fieldDim ghostNo v:= by
       induction v with
       | nil=> rfl
       | cons i v ih=> rw [List.forall_mem_cons] at hL; rw [field_cons]; exact add_nonneg (role_no i hL.1) (ih hL.2)
    induction w with
    | nil=> simp
    | cons i w ih=> rw [List.forall_mem_cons] at hx ⊢; rw [field_cons] at h; have ht:=hl w hx.2; have he:= role_no i hx.1; exact ⟨by omega, ih hx.2 (by omega)⟩
lemma cost_vec (i : Lane4 G) (he:wfield i.1=1) (h:ghostNo i.1=0) : ∃ l k p, i=W l k p:= by
    rcases i with ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> norm_num [wfield,dim] at he <;> norm_num [ghostNo,ghostChannel] at h
    exact ⟨i,c,p,rfl⟩
variable (X: Class F h)
include X
lemma quartic (hh:h≤4) {p q r s:FourP} (a b c d i j k l) (he:p+(q+(r+s))=0): F [W a i p,W b j q,W c k r,W d l s]=0:=by
   let V:=spike a; have hv:= X.closed [C i V,W b j (-V),W c k 0,W d l 0] (by simp [net,C,W,qnote])
   rw [qGhost,qAA,qAA,qAA,q0] at hv; simp_rw [at_D] at hv
   have ht x : F [C i V,U x j (-V), W c k 0,W d l 0]=0:= X.tall _ (by simp [net,C,U,W,qnote]) (by norm_num [fieldDim,wfield,dim,C,U,W,qnote]; omega)
   -- precision on other two at p=0
   have hz x y: precision x y (0:Momentum Axis)=0:=by unfold precision delta Momentum.sq; simp
   simp_rw [ht,hz,Complex.ofReal_zero,neg_zero,mul_zero,zero_mul,Finset.sum_const_zero,add_zero,sub_zero] at hv
   rw [Finset.sum_eq_single a (fun j _ hj=>by simp [V,hj]) (by simp)] at hv
   rw [af_constant X hh [W a i p,W b j q,W c k r,W d l s] [W a i V,W b j (-V),W c k 0,W d l 0] (by simpa [W,net,qnote] using he) (by simp [W,net,qnote]) rfl rfl]; simpa [V] using hv
omit X
lemma large_class (X:Class F h) (hh:h≤4) (r:ℕ) (hr:4≤r): EqualAt r F 0:= by
   intro w hw hp; have hL:= length_pay w
   rcases lt_or_ge 4 (fieldDim wfield w) with h'|h'; exact X.tall _ hw (lt_of_le_of_lt hh h')
   have hv : w.length=4:= by omega
   have hu:=pay_eq w (by omega); by_cases he:fieldDim ghostNo w=0; swap; exact X.ne _ hw he
   have he :=no_eq w hu he
   have hs : ∀ i∈w,∃ a k p,i=W a k p:= fun i hi=> cost_vec i (hu i hi) (he i hi)
   obtain ⟨x,y,z,t,rfl⟩:= List.length_eq_four.mp hv
   rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons] at hs; obtain ⟨⟨a,i,p,rfl⟩,⟨b,j,Q,rfl⟩,⟨c,k,P,rfl⟩,⟨d,l,S,rfl⟩,_⟩:=hs; exact quartic X hh a b c d i j k l (by simpa [net,W,qnote] using hw)
end YM.MS.Landau.Detect
