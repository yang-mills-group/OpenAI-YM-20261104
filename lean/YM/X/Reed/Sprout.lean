import YM.Next.RANK.Keys
import YM.X.Charting.Panes
/-!
Centered difference intertwiner per native-axis polynomial. Symmetric tensors real components with centered factors; prove finite exact rather than power-series truncation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Next.Rank.CellsInt Tensor Filter MeasureTheory Metric Finset Function -- inspect
open scoped Topology ContDiff BigOperators

def whisk : ℕ→ ℝ →ℝ
 | 0, _ => 1
 | n+1,x=> x*∏ i∈ range n,(x+(n+1:ℕ)/2-(i+1:ℕ)) -- check coer
lemma one_jump (x:ℝ)(n:ℕ): whisk (n+1) (x+1/2)-whisk (n+1) (x-1/2) = (n+1:ℕ)* whisk n x:= by
   cases n with
   | zero => simp only [whisk,range_zero,prod_empty,mul_one,Nat.cast_one,Nat.zero_add];ring
   | succ n =>
     let f (i:ℕ):=(x+(n+1:ℕ)/ (2:ℝ)-(i+1:ℕ))
     let P (y : ℝ)(i:ℕ):= y+(n+1+1:ℕ)/(2:ℝ)-(i+1:ℕ)
     have hc i : P (x+1/2) (i+1) = f i := by unfold f P; push_cast; ring
     have ht i : P (x-1/2) i=f i:= by unfold f P; push_cast; ring
     rw [whisk,whisk,whisk]
     change (x+1/2) * (∏ i∈range (n+1), P (x+1/2) i)-(x-1/2)*(∏ i ∈ range (n+1), P (x-1/2) i)= _ * (x*∏ i∈range n,f i); rw [Finset.prod_range_succ' _ n,prod_range_succ (P (x-1/2)),funext ht]; simp only [hc]
     unfold f P; push_cast; ring

variable {V : Type} [NormedAddCommGroup V][NormedSpace ℝ V] {n:ℕ}
def pick (l:Fin n→Axis) (i:Axis): ℕ:= ∑ j,if l j=i then (1:ℕ) else 0
lemma pick_perm (s:Equiv.Perm (Fin n))(l:Fin n→Axis) (i:Axis): pick (l∘s) i=pick l i:= Equiv.sum_comp s fun j=>if l j=i then (1:ℕ) else 0
lemma pick_step (l:Fin n→Axis) (i j:Axis): pick (Fin.cons i l) j=(if i=j then 1 else 0)+pick l j:= by unfold pick; rw [Fin.sum_univ_succ]; simp

def block (l:Axis→ℕ)(x:E4): ℝ:= ∏ i,whisk (l i) (x i)
def low (p:Axis→ℕ)(i:Axis) (j:Axis) : ℕ:= p j - (if i=j then 1 else 0)
def tip (i:Axis):E4:=(1/2:ℝ)•basis i
lemma bump (p:Axis→ℕ)(x:E4)(i:Axis): block p (x+tip i)-block p (x-tip i)=p i * block (low p i) x:= by
    let f(y:E4)(ν:Axis→ℕ)(j:Axis):=whisk (ν j) (y j);let Z:=univ.erase i; let F:=∏ j∈Z,f x p j
    have he(y:E4)(ν:Axis→ℕ)(hy:∀j≠i, y j=x j)(hp:∀j≠i,ν j=p j) : block ν y=F*f y ν i := by unfold block F; rw [←prod_erase_mul _ _ (mem_univ i)]; congr 1; apply prod_congr rfl; intro j hj; unfold f; rw [hy j (mem_erase.mp hj).1,hp j (mem_erase.mp hj).1]
    have ta(j:Axis)(h:j≠i): (tip i) j=0:= by simp [tip,h,h.symm];
    rw [he (x+_) _ (fun j h=>by simp [ta j h]) (fun _ _=>rfl),he (x-_) _ (fun j h=>by simp [ta j h]) (fun _ _=>rfl),he x (low p i) (fun _ _=>rfl) (fun j h=>by simp [low,h,h.symm]), ←mul_sub]
    have hp:(tip i) i=1/2:= by simp [tip]
    unfold f; simp only [PiLp.add_apply, PiLp.sub_apply,hp,low,↓reduceIte]
    generalize p i=b; cases b with
    | zero=> simp [whisk];
    | succ m=> rw [one_jump]; simp only [Nat.add_sub_cancel];ring

def gather (x:E4) : (T E4 V n) →ₗ[ℝ] V where
    toFun A:= ∑ l:Fin n→Axis, block (pick l) x • A (basis ∘ l)
    map_add' A B:= by simp [smul_add,Finset.sum_add_distrib]
    map_smul' r A:= by simp only [smul_apply, Finset.smul_sum, RingHom.id_apply]; simp_rw [smul_comm r]
lemma grab (A:T E4 V (n+1))(x:E4)(i:Axis)(h:Sym A): gather (x+tip i) A-gather (x-tip i) A=(n+1:ℕ) • gather x (A.curryLeft (basis i)):= by
    let f (l:Fin (n+1)→Axis):=block (low (pick l) i) x • A (basis ∘ l); let F (u:Fin (n+1)→Axis)(j:Fin (n+1)):= if u j=i then f u else 0
    change ∑ l:Fin (n+1)→Axis,(_ • _)-∑ l,(_ • _) = _; rw [← sum_sub_distrib]; simp_rw [← sub_smul,bump,mul_smul,Nat.cast_smul_eq_nsmul]
    change ∑ l:Fin (n+1)→Axis,(pick l i • f l)=_; have he(l:Fin (n+1)→Axis): pick l i • f l=∑ j,F l j:= by unfold pick F; rw [sum_smul]; simp only [ite_smul,one_smul,zero_smul];
    have hperm(s:Equiv.Perm (Fin (n+1)))(l:Fin (n+1)→Axis): f (l∘s)=f l:= by unfold f; rw [funext (pick_perm s l),←Function.comp_assoc, h]
    have hu: ∑ l:Fin (n+1)→Axis,F l 0=gather x (A.curryLeft (basis i)):= by
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1)=>Axis)), Fintype.sum_prod_type]; change ∑ k:Axis, ∑ l:Fin n→Axis,F (Fin.cons k l) 0= _
      rw [sum_eq_single i]; swap; · intro k _ h;unfold F; simp [h]
      change ∑ u:Fin n→Axis,F _ 0=∑ l:Fin n→Axis,_; refine sum_congr rfl fun l _=>?_ ; unfold F f; simp only [Fin.cons_zero,↓reduceIte]
      have he : low (pick (Fin.cons i l)) i=pick l:= by funext j; unfold low; rw [pick_step]; omega
      rw [he,ContinuousMultilinearMap.curryLeft_apply]; congr 2; ext1 j; exact Fin.cases rfl (fun _=>rfl) j
      simp
    have hl(j:Fin (n+1)) : ∑ l:Fin (n+1)→Axis,F l j= ∑ l:Fin (n+1)→ Axis,F l 0 := by
      let s:=Equiv.swap j 0; let e:(Fin (n+1)→Axis)≃(Fin (n+1)→Axis):={toFun:= fun l=>l∘s,invFun:=fun l=>l ∘ s.symm,left_inv:=fun l=> funext (by simp), right_inv:=fun l=> funext (by simp)} -- braces sep commas
      refine Fintype.sum_equiv e _ _ fun l=> ?_; change F l j=F (l∘s) 0; unfold F; rw [hperm]; simp [s]
    simp_rw [he];rw [Finset.sum_comm]; simp_rw [show ∀j, ∑ l:Fin (n+1)→Axis,F l j=gather x (A.curryLeft (basis i)) from fun j=> (hl j).trans hu]; simp
end YM.PositionX.Reed
