import YM.OPE.Compatible.Tides.Local
/-!
# Horn monomial. Angular orbit polynomial matches lattice price
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open Pert.Full (incVec)
open scoped BigOperators Classical ContDiff
variable {x:E4}
def arcH (i:Axis)(k:ℕ)(x:E4):= x i^k/(k.factorial:ℝ)
def horn (m:Multiset Axis)(x:E4):= ∏ i, arcH i (m.count i) x
lemma accord (i:Axis)(k:ℕ): PureA k (arcH i k):=by
    refine ⟨?_ ,fun x t=>?_⟩; · unfold arcH; fun_prop
    simp [arcH,mul_pow];ring
lemma horn_plus (i:Axis)(m:Multiset Axis): horn (i ::ₘ m) = ((((m.count i+1:ℕ):ℝ))⁻¹) • (coordF i * horn m):=by
    funext x; unfold horn; rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i),Pi.smul_apply,Pi.mul_apply,←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]; rw [show (∏ j∈Finset.univ.erase i,arcH j ((i ::ₘ m).count j) x)=∏ j∈Finset.univ.erase i, arcH j (m.count j) x from Finset.prod_congr rfl (fun j h=>by rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase h)])]; rw [Multiset.count_cons_self]; unfold arcH coordF; simp only [Nat.factorial_succ,smul_eq_mul,Nat.cast_mul]; rw [div_eq_mul_inv,mul_inv]; ring
lemma horn_pure (m:Multiset Axis):PureA m.card (horn m):=by
    induction m using Multiset.induction with
    | empty=> rw [show horn 0=(1:E4→ℝ) from funext fun x=>by simp [horn,arcH]]; exact ⟨contDiff_const,fun _ _=>by simp⟩
    | cons i v ih=> rw [horn_plus,Multiset.card_cons,add_comm]; exact (pure_multiply (pure_coordF _) ih).vScale _
lemma blowing (m:Multiset Axis)(i:Axis): grad i (horn m)= if i∈ m then horn (m.erase i) else 0:=by
   induction m using Multiset.induction with
   | empty=> rw [show horn 0=(1:E4→ℝ) from funext fun x=>by simp [horn,arcH]]; funext x; simp [grad,D]
   | cons j m ih=>
      funext x; have hs:= (pure_coordF j).smooth; have hw:=(horn_pure m).smooth; let t:ℝ:= ((m.count j+1:ℕ):ℝ)⁻¹
      rw [horn_plus,grad_smul (show ContDiffAt ℝ ∞ (coordF j*horn m) x from hs.contDiffAt.mul hw.contDiffAt), Gp _ _ hs.contDiffAt hw.contDiffAt,grad_coordF,ih]; by_cases he:i=j
      · subst j; rw [if_pos (by simp), if_pos (by simp : i∈ i ::ₘ m), Multiset.erase_cons_head]; by_cases hp:i∈m; swap
        · rw [if_neg hp, Multiset.count_eq_zero.mpr hp]; simp
        have hx: coordF i x *horn (m.erase i) x=(m.count i:ℝ)*horn m x:=by
            have e : (((m.erase i).count i + 1:ℕ):ℝ)= (m.count i:ℝ):=by rw [Multiset.count_erase_self]; have ht:=Multiset.count_pos.mpr hp; exact_mod_cast (show m.count i-1+1=m.count i by omega)
            have hz:=horn_plus i (m.erase i); rw [Multiset.cons_erase hp,e] at hz; have he:=congrFun hz x; rw [he]; simp only [Pi.mul_apply, Pi.smul_apply,smul_eq_mul]; have hv:(m.count i:ℝ)>0:=by exact_mod_cast Multiset.count_pos.mpr hp
            field_simp
        rw [if_pos hp,hx]; push_cast; change (↑(m.count i)+1:ℝ)⁻¹*_=_; field_simp;ring
      · by_cases hi:i∈m
        · rw [if_neg he,if_pos hi, if_pos (Multiset.mem_cons_of_mem hi),Multiset.erase_cons_tail _ (Ne.symm he),horn_plus, Multiset.count_erase_of_ne (Ne.symm he)]; simp
        rw [if_neg he,if_neg hi,if_neg (by simp [hi,he])]; simp
lemma pineHook (i:Axis)(m:Multiset Axis)(x:Cover): pine (i ::ₘ m) x= ((x i:ℝ)-(m.count i:ℝ))/((m.count i+1:ℕ):ℝ) * pine m x:=by
   unfold pine; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),← Finset.mul_prod_erase _ (fun j=> pedal (x j) (m.count j)) (Finset.mem_univ i), show (∏ j∈Finset.univ.erase i,pedal (x j) ((i ::ₘ m).count j))=(∏ j∈Finset.univ.erase i,pedal (x j) (m.count j)) from Finset.prod_congr rfl (fun j hj=>by rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hj)]),Multiset.count_cons_self,pedal]; push_cast;ring
lemma pine_quip (m:Multiset Axis): Quip (-(m.card:ℤ)) (pine m) (horn m):=by
   induction m using Multiset.induction with
   | empty=> intro n x hn p hp hx; simp [quilting,horn,pine,pedal,arcH]
   | cons i m ih=>
     let v:= m.count i; let t:=v+1; let A(x:Cover):=((x i:ℝ)-(v:ℝ))/(t:ℝ); let B:= ((t:ℝ))⁻¹ • coordF i; rw [funext (fun x : Cover=>pineHook i m x)] -- invalid rw funext
     have he: Quip (-1) A B:=by
         intro n x hn p hp hx; let z:= fun j=> n j; have hv:= (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (tendsto_natCast_atTop_atTop.comp hn)
         have hk: Tendsto (fun j=>dew (z j)) atTop (𝓝 0):=hv
         have hh:= (pure_coordF i).smooth.continuous.continuousAt.tendsto.comp hx
         have ht :B p= (coordF i p-(0:ℝ)*v)/(t:ℝ):=by unfold B;simp;ring
         rw [ht]; refine ((hh.sub (hk.mul_const (v:ℝ))).div_const _).congr (fun j=>?_); unfold quilting; rw [neg_neg,zpow_one]; change ((dew (z j)*(x j i:ℝ)-dew (z j)*↑v)/(t:ℝ))=dew (z j)*A (x j); unfold A; ring
     rw [horn_plus,show ((t:ℝ)⁻¹) • (coordF i * horn m)=B*horn m from (smul_mul_assoc ..).symm]; simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one,neg_add]; rw [add_comm (-(m.card:ℤ))]; convert! he.purse ih using 2; unfold A t; simp only [Pi.mul_apply,Nat.cast_add,Nat.cast_one]; rfl
end YM.OPE.Balsam
