import YM.RG11Scheme.Bell.Steps

/-! Solving the lattice Poisson equation on cover polynomial jets, both real forward and backward slices. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Bell
open Function Mesh Lattice Stencil Stencil.Shot
open scoped BigOperators Classical Topology
variable {E:Type} [AddCommGroup E] {f B:Cover → E}
local notation "τ" => (0:Axis)
local notation "t'" => (step τ:Cover)
local notation "I" => (Finset.univ.erase τ)

-- coordinate replace
def pane (m:ℤ)(x:Cover) := update x τ m
@[simp] lemma pane_act (x:Cover) : pane (x τ) x=x:= update_eq_self ..
lemma pane_aim (m:ℤ)(x:Cover) : pane m (pane 0 x)=pane m x := by unfold pane; rw [update_idem]
lemma pane_plus (x:Cover)(m:ℤ): pane m (x+t')=pane m x := by funext i;by_cases h:i=τ <;> simp [pane,h]
lemma pane_minus (x:Cover)(m:ℤ): pane m (x-t')=pane m x := by nth_rw 2 [←sub_add_cancel x t'];rw [pane_plus]
lemma pane_slide (x:Cover) (i:Axis) (m:ℤ)(hi:i≠τ) : pane m (x+step i)=pane m x+step i := by funext k;by_cases h:k=τ <;> simp [pane,h,hi,ne_comm]
lemma pane_backward (x:Cover) (i:Axis) (m:ℤ)(hi:i≠τ) : pane m (x-step i)=pane m x-step i := by apply eq_sub_of_add_eq;rw [← pane_slide _ _ _ hi,sub_add_cancel]
lemma step_up (x:Cover) (i:Axis)(h:i≠τ): (x+step i:Cover) τ=x τ := by simp [h,ne_comm]
lemma step_down (x:Cover) (i:Axis)(h:i≠τ): (x-step i:Cover) τ=x τ := by simp [h,ne_comm]

lemma recursive_clock (Q:Type)(Y:ℤ→ Q≃Q)(v:Q) : ∃ F:ℤ→Q,F 0=v∧ ∀ i:ℤ,F (i+1)=Y i (F i) := by
   let F (i:ℤ):= Int.inductionOn' (motive:=fun _=> Q) i 0 v (fun i _ p=> Y i p) (fun i _ p=> (Y (i-1)).symm p)
   refine ⟨F,Int.inductionOn'_self,?_⟩; intro i
   by_cases h:0≤ i
   · exact Int.inductionOn'_add_one (motive:=fun _=>Q) (succ:=fun i _ p=>Y i p) (pred:= fun i _ p=> (Y (i-1)).symm p) (zero:=v) h
   have ht : i+1≤0:= by omega
   have he:F (i+1-1)=(Y (i+1-1)).symm (F (i+1)):= Int.inductionOn'_sub_one (motive:=fun _=>Q) (succ:=fun i _ p=>Y i p) (pred:= fun i _ p=> (Y (i-1)).symm p) (zero:=v) ht
   rw [add_sub_cancel_right] at he
   rw [he,Y i|>.apply_symm_apply]

def stoptime (U : Cover→ E) (i:Axis) x:= U (x+step i)+U (x-step i)-2 • U x
def offwalk (U : Cover→E) (x:Cover) := ∑ i∈I,stoptime U i x
lemma garden (U:Cover→E)(x:Cover) : quake U x=offwalk U x+stoptime U τ x:= by unfold offwalk;rw [Finset.sum_erase_add _ _ (Finset.mem_univ _)]; rfl

private def stay (f:Cover→ E) (i:ℤ) (g : Cover→E) (x:Cover) := f (pane (i+1) x) + 2 • g x - offwalk g x
local notation "Ξ" => (Cover→ E) × (Cover→ E)
def timely (f:Cover→ E)(i:ℤ): Ξ≃Ξ where
   toFun p:=⟨p.2,stay f i p.2-p.1⟩
   invFun p:=⟨stay f i p.1-p.2,p.1⟩
   left_inv p:= by simp
   right_inv p:= by simp
lemma globe (f:Cover→ E): ∃ U:Cover→ E, quake U=f ∧ (∀ x,x τ=0 → U x=0) ∧ (∀ x,x τ=1→ U x=0) := by
   obtain ⟨P,h,H⟩:=recursive_clock Ξ (timely f) 0
   let A (i:ℤ):= (P i).1
   have hp (i:ℤ): (P i).2=A (i+1) := by unfold A; rw [H]; exact rfl
   have hw (i:ℤ)(x:Cover) : A (i+1) x=stay f (i-1) (A i) x - A (i-1) x:= by
       have he:=congrArg Prod.snd (H (i-1));
       dsimp only [timely] at he;change (P (i-1+1)).2= stay f (i-1) (P (i-1)).2-A (i-1) at he; rw [hp,hp, sub_add_cancel] at he; exact congrFun he x
   let U (x:Cover):=A (x τ) (pane 0 x)
   have hx (x): offwalk U x= offwalk (A (x τ)) (pane 0 x):= by
       apply Finset.sum_congr rfl; intro i hi
       unfold stoptime U; rw [step_up _ _ (Finset.ne_of_mem_erase hi),step_down _ _ (Finset.ne_of_mem_erase hi),pane_slide _ _ _ (Finset.ne_of_mem_erase hi),pane_backward _ _ _ (Finset.ne_of_mem_erase hi)]
   refine ⟨U,funext fun x=> ?_,fun x hx=> ?_,fun x hc=>?_⟩
   · rw [garden,hx]; unfold stoptime U; rw [pane_plus,pane_minus]; simp only [Pi.add_apply,Pi.sub_apply, step_apply, if_true]; rw [hw (x τ),stay,pane_aim,show x τ-1+1=x τ by omega,pane_act]; abel
   · simp only [U,A,hx,h]; exact rfl
   unfold U;rw [hc, ← show (0:ℤ)+1=1 from by norm_num,← hp 0,h];exact rfl -- shadow name

lemma falls (u:ℤ)(f:Cover→ E)(h:∀ x,x τ=u→f x=0) : ∀ x,x τ=u→ offwalk f x=0 := fun x hx=> Finset.sum_eq_zero (fun i hi=>by rw [stoptime,h x hx,h _ ((step_up x i (Finset.ne_of_mem_erase hi)).trans hx),h _ ((step_down x i (Finset.ne_of_mem_erase hi)).trans hx)]; simp)
lemma inhabit (f:Cover→ E)(he:quake f=0)(hz:∀ x,x τ=0 → f x=0)(ht:∀ x,x τ=1→ f x=0) : f=0 := by
   let P (i:ℤ):= ∀ x,x τ=i →f x=0
   have ex x:=congrFun he x
   simp_rw [garden,stoptime] at ex
   have H (u:ℤ):P u∧ P (u+1) := by
      induction u using Int.inductionOn' (b:=0) with
      | zero=> exact ⟨hz, ht⟩
      | succ i _ IH=>
         refine ⟨IH.2, fun x hc=>?_⟩; let z:=x-t';have hl : z τ=i+1 := by simp [z,hc]
         have hm : (z-t') τ=i:= by rw [Pi.sub_apply,hl,step_apply,if_pos rfl]; ring
         have hu := ex z;rw [IH.1 _ hm, IH.2 _ hl, falls (i+1) f IH.2 _ hl, show z+t'=x from sub_add_cancel ..] at hu
         simpa only [Pi.zero_apply,smul_zero,zero_add,add_zero,sub_zero] using hu
      | pred i _ IH=>
         refine ⟨fun x hx=>?_, (sub_add_cancel i 1).symm ▸ IH.1⟩
         let z:=x+t';have hl : z τ=i:= by simp [z,hx];
         have hm : (z+t') τ=i+1:=by simp [hl]
         have hu := ex z; rw [IH.2 _ hm, IH.1 _ hl, falls i f IH.1 _ hl, show z-t'=x from add_sub_cancel_right ..] at hu; simpa only [Pi.zero_apply,smul_zero,sub_zero,zero_add] using hu
   exact funext fun x=>(H (x τ)).1 x rfl
end YM.RG11Scheme.Bell
