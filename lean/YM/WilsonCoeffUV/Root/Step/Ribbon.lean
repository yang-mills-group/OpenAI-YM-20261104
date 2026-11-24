import YM.WilsonCoeffUV.Root.Step.Ledger
/-! # Ledger crossing using untouched pivot. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open scoped Topology BigOperators
variable {n:Side}{U α β V ι E : Type*}{k r l j:ℕ} {A B C D X Y σ η : ℝ} {d:Distance U}{w:U}{p:Cover}

lemma across (d:Distance U)(p:U)(x:dock U β r)(y:dock U α r): brims d p x y ≤ tread d p y + ∑ i,d.gap (y i).1 (x i).1 := by
    let X:dock U Unit (r+1):= fun i=>(stud p x i,())
    let Y:dock U Unit (r+1):= fun i=>(stud p y i, ())
    have he:= drag_len d X Y
    rw [Fin.sum_univ_succ,show d.gap (Y 0).1 (X 0).1=0 from d.self _,zero_add] at he
    have hx : ∀ i,(Y (Fin.succ i)).1=(y i).1:= fun i=>by simp [Y,stud]
    have hv : ∀ i,(X (Fin.succ i)).1=(x i).1:= fun i=>by simp [X,stud]
    simp_rw [hx,hv] at he; refine le_trans (league_le d _ fun i j=>?_) he
    let f:= Sum.elim (Prod.fst ∘ X) (Prod.fst ∘ Y); let g:= Sum.elim (stud p x) (Prod.fst ∘ y)
    have hy i: ∃ j,f j=g i:=by cases i with
                                | inl i=> exact ⟨Sum.inl i,rfl⟩
                                | inr i=> exact ⟨Sum.inr (Fin.succ i),hx i⟩
    change d.gap (g i) (g j)≤ league d f; obtain ⟨a,ha⟩:=hy i; obtain ⟨b,hb⟩:=hy j; rw [←ha,←hb]; exact leg_le d f _ _

variable [NormedAddCommGroup V][NormedSpace ℝ V]
lemma palmcash_ribbon {G:Fin r→ ropes U α β}{P:Ten V (U×α) r}{K:Fin r→ℝ}(h:∀ i, dragCup d σ (K i) (G i))(e:Cork d w σ A P)(he:0≤σ) : Peb d w σ ((∏ i,K i)*A) (ribbon G P):=by
  refine ⟨mul_nonneg (Finset.prod_nonneg fun i _=> (h i).1) e.1,fun x y=>?_⟩
  have hg : ‖∏ i,G i (y i) (x i)‖ ≤ ∏ i, K i*Real.exp (-σ*d.gap (y i).1 (x i).1):= by
    rw [Real.norm_eq_abs,Finset.abs_prod]; exact Finset.prod_le_prod (fun _ _=> abs_nonneg _) (fun i _=> (h i).2 ..)
  have hv : ∏ i : Fin r, Real.exp (-σ*d.gap (y i).1 (x i).1)=Real.exp (-σ*(∑ i,d.gap (y i).1 (x i).1 : ℕ)) := by rw [Nat.cast_sum,Finset.mul_sum, Real.exp_sum]
  rw [ribbon,norm_smul]
  apply le_trans (mul_le_mul hg (e.2 y) (norm_nonneg _) ((norm_nonneg _).trans hg)); rw [Finset.prod_mul_distrib,hv,mul_mul_mul_comm,← Real.exp_add, ←mul_add]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Finset.prod_nonneg fun i _=> (h i).1) e.1)
  rw [Real.exp_le_exp]; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr he)
  rw [add_comm,← Nat.cast_add]; exact_mod_cast across d w x y

lemma palmgloss_cup {G: ropes U α β}{P:Ten V (U×α) r}(h:dragCup d σ B G)(e:Cork d w σ A P)(he:0≤σ): Peb d w σ (B^r*A) (gloss G P):= by simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using palmcash_ribbon (fun _: Fin r=>h) e he

-- pivot argument instead of geometric difference, Lipschitz on bounded strips
private def changeSlot (G H:ropes U α β)(r k:ℕ)(i:Fin r): ropes U α β:= if i.val<k then H else G
private lemma ribbon_chain {r:ℕ}(G H:ropes U α β)(k:ℕ)(hk:k<r)(P:Ten V (U×α) r):
    ribbon (changeSlot G H r (k+1)) P = ribbon (fun i=> if i=⟨k,hk⟩ then H-G else changeSlot G H r k i) P + ribbon (changeSlot G H r k) P := by
  let j : Fin r:=⟨k,hk⟩
  funext x y; simp only [Pi.add_apply,ribbon]
  let b i (M:ropes U α β):= M (y i) (x i); let g i:= b i (changeSlot G H r k i); let h i:= b i (changeSlot G H r (k+1) i); let l i:= b i (if i=j then H-G else changeSlot G H r k i)
  have hv : (∏ i,h i)= (∏ i,l i)+(∏ i,g i):= by
    let K:=Finset.univ.erase j; have he i (hi:i∈K): l i=g i ∧ h i=g i := by
      have hf := (Finset.mem_erase.mp hi).1
      refine ⟨by simp [l,g,hf],?_⟩
      have hm : i.val ≠ k:=fun H=> hf (Fin.ext H)
      unfold h g; simp only [changeSlot,show i.val<k+1 ↔ i.val<k by omega]
    rw [← Finset.mul_prod_erase _ h (Finset.mem_univ j), ← Finset.mul_prod_erase _ l (Finset.mem_univ j), ← Finset.mul_prod_erase _ g (Finset.mem_univ j), show (∏ i∈K,h i) = _ from Finset.prod_congr rfl fun i hi=> (he i hi).2, show (∏ i∈K,l i) = _ from Finset.prod_congr rfl fun i hi=> (he i hi).1]
    rw [← add_mul]; congr 1; simp [h,g,l,b,changeSlot,j]
  rw [← add_smul]; exact congr_arg (· • _) hv
private lemma ribbon_gap {G H:ropes U α β}{P:Ten V (U×α) r}(hg:dragCup d σ B G)(hh:dragCup d σ B H)(hv:dragCup d σ D (H-G))(hp:Cork d w σ A P)(ht:0≤σ)(k:ℕ)(hk:k≤r):
    Peb d w σ (k*(D*B^(r-1)*A)) (ribbon (changeSlot G H r k) P-gloss G P):=by
  induction k with
  | zero=> rw [show changeSlot G H r 0=(fun _=>G) from funext fun i=>if_neg (Nat.not_lt_zero _), show ribbon _ _ - _=0 from sub_self (gloss G P),Nat.cast_zero,zero_mul]; exact Peb.zero
  | succ k ih=>
    let j:Fin r:=⟨k,by omega⟩
    have he i: dragCup d σ (if i=j then D else B) (if i=j then H-G else changeSlot G H r k i):= by
      by_cases hf:i=j; simp only [hf,↓reduceIte]; exact hv
      simp only [hf,↓reduceIte,changeSlot]; split; exact hh
      exact hg
    have hl:= palmcash_ribbon he hp ht
    let S : Fin r→ℝ := fun i=>if i=j then D else B
    have hB : (∏ i,S i)=D*B^(r-1):=by
      rw [← Finset.mul_prod_erase _ S (Finset.mem_univ j), show S j=D from if_pos rfl]; congr 1
      rw [← show (Finset.univ.erase j).card=r-1 from by simp, ← Finset.prod_const]; apply Finset.prod_congr rfl
      intro i hi; exact if_neg (Finset.mem_erase.mp hi).1
    rw [show (∏ i, if i=j then D else B)= D*B^(r-1) from hB] at hl
    rw [ribbon_chain G H k (by omega), add_sub_assoc,Nat.cast_add, Nat.cast_one,add_mul,one_mul, add_comm ((k:ℝ)*_)]; exact hl.add (ih (by omega))

lemma palmgloss_gap {G H:ropes U α β}{P Q:Ten V (U×α) r}(hg:dragCup d σ B G)(hh:dragCup d σ B H)(hv:dragCup d σ D (H-G))(hp:Cork d w σ A P)(hu:Cork d w σ C (Q-P))(ht:0≤σ):
    Peb d w σ ((B^r*C)+r*(D*B^(r-1)*A)) (gloss H Q-gloss G P):=by
  have he:= ribbon_gap hg hh hv hp ht r le_rfl
  rw [show changeSlot G H r r=(fun _=>H) from funext fun i=> if_pos i.isLt] at he
  have hh' : gloss H Q-gloss G P=gloss H (Q-P)+(gloss H P-gloss G P):=by simp only [gloss]; funext x y; simp only [ribbon,Pi.sub_apply,Pi.add_apply,smul_sub]; abel
  rw [hh']; exact (palmgloss_cup hh hu ht).add he

variable [Fintype α]
lemma solo_cast {G:ropes Cover α β} {P:Ten V (Cloth α) r}(h:dragCup Bank.terrain σ B G)(e:Cork Bank.terrain p σ A P)(hh:0≤η)(ht:η<σ):
    Cork Bank.terrain p η ((B^r*A)*tiePay α r (σ-η)) (reflectCut G P):=by
    have he : reflectCut G P=ruins (gloss G P):=funext fun x=>climb_cut G x
    rw [he]; exact (palmgloss_cup h e (by linarith)).meter ht hh
variable [CompleteSpace V]
lemma solo_gap {G H:ropes Cover α β} {P Q:Ten V (Cloth α) r}(h:dragCup Bank.terrain σ B G)(h':dragCup Bank.terrain σ B H)(u:dragCup Bank.terrain σ D (H-G))(e:Cork Bank.terrain p σ A P)(q:Cork Bank.terrain p σ A Q)(f:Cork Bank.terrain p σ C (Q-P))(hh:0≤η)(ht:η<σ):
    Cork Bank.terrain p η (((B^r*C)+r*(D*B^(r-1)*A))*tiePay α r (σ-η)) (reflectCut H Q-reflectCut G P):=by
    have hx:0<σ:= by linarith
    rw [show reflectCut G P=ruins (gloss G P) from funext fun x=>climb_cut .., show reflectCut H Q=ruins (gloss H Q) from funext fun x=>climb_cut .., ← (palmgloss_cup h' q hx.le).minus (palmgloss_cup h e hx.le) hx]; exact (palmgloss_gap h h' u e f hx.le).meter ht hh

lemma solo_flash {G:ropes Cover α β}{R:(n:Side)→ ropes (Site n) α β}{P:Gen V (Cloth α)}{Q:(n:Side)→ Gen V (Co n α)}(h:Pilots R G)(e:Bends p (fun n=>Q n r) (P r)): Bends p (fun n=> fade (R n) (Q n) r) (Bank.prism G P r):=by
    obtain ⟨s,a,hp,H⟩:=h.fees; obtain ⟨t,b,ht,J⟩:=e.price; set w:=min s t; have hw:=lt_min hp ht
    have he:Paves p (fun n=>gloss (R n) (Q n r)) (gloss G (P r)) :=⟨fun x y=> (tendsto_finsetProd _ (fun i _=>h.point (y i) (x i))).smul (e.point y),w,_,hw,(H.and J).mono fun _ ⟨hg,hy⟩=> palmgloss_cup (hg.mono (min_le_left ..)) (hy.mono (min_le_right ..)) hw.le⟩
    rw [show Bank.prism G P r=ruins (gloss G (P r)) from funext fun x=>climb_cut ..]; exact he.rest
end YM.WilsonCoeffUV.Soil
