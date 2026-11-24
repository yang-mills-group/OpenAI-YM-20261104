import YM.WilsonCoeffUV.Thermo.Matrix
/-!
# Slot substitutions and perturbed differences. Preserve reserve for SAME-RANK
inheritance (later). Only proper width shrinking when walking job.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r:ℕ} {A B D C σ η : ℝ}
variable {d:Distance U}

lemma drag_len (d:Distance U)(x:dock U β k)(y:dock U α k): course d x y ≤ soar d y + ∑ i,d.gap (y i).1 (x i).1 := by
  let f:=Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)
  let g (i:Fin k):= d.gap (y i).1 (x i).1
  have h₁ (i:Fin k):g i≤∑ i,g i:= Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ _)
  have hv (i j:Fin k): d.gap (y i).1 (y j).1≤soar d y:=leg_le d (Prod.fst ∘ y) i j
  have hy (i j : Fin k): d.gap (f (.inr i)) (f (.inl j)) ≤ soar d y +∑ k,g k := (d.tri (y i).1 (y j).1 (x j).1).trans (Nat.add_le_add (hv _ _) (h₁ _))
  refine league_le _ _ fun i j=>?_; change d.gap (f i) (f j)≤soar d y + ∑ k,g k
  cases i with
  | inr i=> cases j with
             | inl j=> exact hy i j
             | inr j=> exact (hv i j).trans (Nat.le_add_right ..)
  | inl i=> cases j with
             | inr j=> rw [d.swap]; exact hy _ _
             | inl j=>
               by_cases he:i=j; simp [he,d.self]
               have hw:g i+g j≤∑ k,g k:= by
                 apply le_trans _ (Finset.sum_le_sum_of_subset (f:=g) (Finset.subset_univ {i,j}))
                 simp [he]
               change d.gap (x i).1 (x j).1≤_
               have h:= d.tri (x i).1 (y i).1 (x j).1; rw [d.swap (x i).1 (y i).1] at h
               exact h.trans ((Nat.add_le_add_left ((d.tri (y i).1 (y j).1 (x j).1).trans (Nat.add_le_add_right (hv i j) (g j))) (g i)).trans (by
                  change g i+ (soar d y+g j)≤soar d y+∑ k,g k; omega))

section
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

def ribbon (G:Fin r→ ropes U α β)(P:Ten V (U×α) r): canal U α β V r r:= fun x y=> (∏ i,G i (y i) (x i)) • P y
lemma cash_ribbon {G:Fin r→ ropes U α β}{P:Ten V (U×α) r}{K:Fin r→ℝ}(h:∀ i, dragCup d σ (K i) (G i))(e:Amber d σ A P)(he:0≤σ) : pairCup d σ ((∏ i,K i)*A) (ribbon G P):=by
  refine ⟨mul_nonneg (Finset.prod_nonneg fun i _=> (h i).1) e.1,fun x y=>?_⟩
  have hg : ‖∏ i,G i (y i) (x i)‖ ≤ ∏ i, K i*Real.exp (-σ*d.gap (y i).1 (x i).1):= by
    rw [Real.norm_eq_abs,Finset.abs_prod]; exact Finset.prod_le_prod (fun _ _=> abs_nonneg _) (fun i _=> (h i).2 ..)
  have hv : ∏ i : Fin r, Real.exp (-σ*d.gap (y i).1 (x i).1)=Real.exp (-σ*(∑ i,d.gap (y i).1 (x i).1 : ℕ)) := by rw [Nat.cast_sum,Finset.mul_sum, Real.exp_sum]
  rw [ribbon,norm_smul]
  apply le_trans (mul_le_mul hg (e.2 y) (norm_nonneg _) ((norm_nonneg _).trans hg)); rw [Finset.prod_mul_distrib,hv,mul_mul_mul_comm,← Real.exp_add, ←mul_add]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Finset.prod_nonneg fun i _=> (h i).1) e.1)
  rw [Real.exp_le_exp]; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr he)
  rw [add_comm,← Nat.cast_add]; exact_mod_cast drag_len d x y

abbrev gloss {U α β:Type*} (G:ropes U α β) (P:Ten V (U×α) r):= ribbon (fun _=>G) P
lemma gloss_cup {G: ropes U α β}{P:Ten V (U×α) r}(h:dragCup d σ B G)(e:Amber d σ A P)(he:0≤σ): pairCup d σ (B^r*A) (gloss G P):= by simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using cash_ribbon (fun _: Fin r=>h) e he

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
private lemma ribbon_gap {G H:ropes U α β}{P:Ten V (U×α) r}(hg:dragCup d σ B G)(hh:dragCup d σ B H)(hv:dragCup d σ D (H-G))(hp:Amber d σ A P)(ht:0≤σ)(k:ℕ)(hk:k≤r):
    pairCup d σ (k*(D*B^(r-1)*A)) (ribbon (changeSlot G H r k) P-gloss G P):=by
  induction k with
  | zero=> rw [show changeSlot G H r 0=(fun _=>G) from funext fun i=>if_neg (Nat.not_lt_zero _), show ribbon _ _ - _=0 from sub_self (gloss G P),Nat.cast_zero,zero_mul]; exact pairCup.zero
  | succ k ih=>
    let j:Fin r:=⟨k,by omega⟩
    have he i: dragCup d σ (if i=j then D else B) (if i=j then H-G else changeSlot G H r k i):= by
      by_cases hf:i=j; simp only [hf,↓reduceIte]; exact hv
      simp only [hf,↓reduceIte,changeSlot]; split; exact hh
      exact hg
    have hl:= cash_ribbon he hp ht
    let S : Fin r→ℝ := fun i=>if i=j then D else B
    have hB : (∏ i,S i)=D*B^(r-1):=by
      rw [← Finset.mul_prod_erase _ S (Finset.mem_univ j), show S j=D from if_pos rfl]; congr 1
      rw [← show (Finset.univ.erase j).card=r-1 from by simp, ← Finset.prod_const]; apply Finset.prod_congr rfl
      intro i hi; exact if_neg (Finset.mem_erase.mp hi).1
    rw [show (∏ i, if i=j then D else B)= D*B^(r-1) from hB] at hl
    rw [ribbon_chain G H k (by omega), add_sub_assoc,Nat.cast_add, Nat.cast_one,add_mul,one_mul, add_comm ((k:ℝ)*_)]; exact hl.add (ih (by omega))

lemma gloss_gap {G H:ropes U α β}{P Q:Ten V (U×α) r}(hg:dragCup d σ B G)(hh:dragCup d σ B H)(hv:dragCup d σ D (H-G))(hp:Amber d σ A P)(hu:Amber d σ C (Q-P))(ht:0≤σ):
    pairCup d σ ((B^r*C)+r*(D*B^(r-1)*A)) (gloss H Q-gloss G P):=by
  have he:= ribbon_gap hg hh hv hp ht r le_rfl
  rw [show changeSlot G H r r=(fun _=>H) from funext fun i=> if_pos i.isLt] at he
  have hh' : gloss H Q-gloss G P=gloss H (Q-P)+(gloss H P-gloss G P):=by simp only [gloss]; funext x y; simp only [ribbon,Pi.sub_apply,Pi.add_apply,smul_sub]; abel
  rw [hh']; exact (gloss_cup hh hu ht).add he

variable [Fintype α]
def reflectCut (G:ropes Cover α β){r:ℕ} (P:Ten V (Cloth α) r) : Ten V (Cloth β) r:= match r with
| 0=> fun _=> P default
| _+1=> worn (gloss G P)
omit [Fintype α] in
lemma climb_cut (G:ropes Cover α β){P:Ten V (Cloth α) r}(x): reflectCut G P x=∑' y:dock Cover α r,(∏ i,G (y i) (x i)) • P y:= by
  cases r with
  | zero=> simp [reflectCut]
  | succ r=> unfold reflectCut worn; exact tsum_congr fun i=>if_neg (by omega)
lemma reflect_eta {G:ropes Cover α β} {P:Ten V (Cloth α) r}(h:dragCup terrain σ B G)(e:Amber terrain σ A P)(hh:0≤η)(ht:η<σ):
    Amber terrain η (if r=0 then A else (B^r*A)*tiePay α r (σ-η)) (reflectCut G P):=by
  cases r with
  | zero=> refine ⟨by simpa only [↓reduceIte] using e.1, fun x=>?_⟩; simpa [reflectCut,soar,league] using ((e.mono ht.le).2 default)
  | succ r=> rw [if_neg (by omega)]; exact worn_amber (gloss_cup h e (by linarith)) hh ht

variable [CompleteSpace V]
lemma reflect_gap {G H:ropes Cover α β} {P Q:Ten V (Cloth α) r}(h:dragCup terrain σ B G)(h':dragCup terrain σ B H)(u:dragCup terrain σ D (H-G))(e:Amber terrain σ A P)(q:Amber terrain σ A Q)(f:Amber terrain σ C (Q-P))(hh:0≤η)(ht:η<σ):
    Amber terrain η (if r=0 then C else ((B^r*C)+r*(D*B^(r-1)*A))*tiePay α r (σ-η)) (reflectCut H Q-reflectCut G P):=by
  have hx:0<σ:= by linarith
  cases r with
  | zero=> refine ⟨by simpa only [↓reduceIte] using f.1, fun x=>?_⟩; simpa [reflectCut,soar,league] using ((f.mono ht.le).2 default)
  | succ r=>
    rw [reflectCut,reflectCut, ← worn_sub (gloss_cup h' q hx.le) (gloss_cup h e hx.le) hx,if_neg (by omega)]
    exact worn_amber (gloss_gap h h' u e f hx.le) hh ht

variable {G:ropes Cover α β}{R:(n:Side)→ ropes (Site n) α β}{P:Gen V (Cloth α)}{Q:(n:Side)→ Gen V (Co n α)}
omit [Fintype α] [CompleteSpace V] in
lemma Tremor.ribbon {P:raw α V (k+1)}{Q:Ten V (Cloth α) (k+1)}(h:Pilots R G)(e:Yields P Q): Tremor (fun n=>gloss (R n) (P n)) (gloss G Q):= by
  obtain ⟨s,b,hp,H⟩ :=h.fees; obtain ⟨t,a,ht,J⟩:=e.fees
  have hy n: dilute P n=P n:= if_neg (by omega)
  set w:=min s t; have hw:0<w:= lt_min hp ht
  refine ⟨fun x y=> ?_, ?_,w,_,hw,(H.and J).mono (fun n ⟨he,hx⟩=>by rw [hy] at hx; exact gloss_cup (he.mono (min_le_left ..)) (hx.mono (min_le_right ..)) hw.le)⟩
  · have he:= e.point y; simp_rw [hy] at he
    exact (tendsto_finsetProd _ (fun i _=>h.point (y i) (x i))).smul he
  filter_upwards [h.move,e.strolls] with n hn he; intro b x y
  unfold gloss Bank.ribbon; rw [he b y]; congr 1; exact Finset.prod_congr rfl fun i _=> hn b _ _

def prism (G:ropes Cover α β)(P:Gen V (Cloth α)): Gen V (Cloth β):= fun i=> reflectCut G (P i)
lemma prism_fold (h:Pilots R G)(e:Yields (fun n=>Q n r) (P r)): Yields (fun n=> fade (R n) (Q n) r) (prism G P r):=by
  cases r with
  | zero=>
    have hh n x: dilute (fun n=> fade (R n) (Q n) 0) n x=dilute (fun n=>Q n 0) n default:= by simp [dilute,fade]
    obtain ⟨s,a,hp,H⟩:=e.fees
    refine ⟨fun i=>?_,Eventually.of_forall fun n b x=> congrArg (fade _ _ 0) (Subsingleton.elim _ _),s,a,hp,H.mono fun n hn=>⟨hn.1,fun x=>?_⟩⟩
    · simp_rw [hh]
      refine (e.point default).congr' (Eventually.of_forall fun i=>?_); congr; exact Subsingleton.elim _ _
    rw [hh]; simpa [soar,league] using hn.2 default
  | succ r=> exact (Tremor.ribbon h e).transfers
end
end YM.WilsonCoeffUV.Bank
