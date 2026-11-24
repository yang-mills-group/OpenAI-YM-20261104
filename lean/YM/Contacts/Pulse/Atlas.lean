import YM.Contacts.Pulse.Preserve
/-! Periodizing allAt on finite ranks. A dependent placement computation rather
than finite offset interpolation. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Set Filter Finset RG Push.AbsoluteSums MergeProof Extra.Iteration
open scoped Topology BigOperators Classical NNReal
variable {n:ℕ}{ι X Y A B C D : Type*}
variable {f:Fin n→ X→ℝ}{g:Fin n→Y→ℝ} {p:X→Y}

-- equating constrained sums across independent residual positions
lemma Scroll.pi (hf:∀ i, Summable (f i))(h:∀ i, Scroll p (f i) (g i)): Scroll (fun r:Fin n→ X=>p∘ r) (fun r=>∏ i:Fin n,f i (r i)) (fun r:Fin n→ Y=>∏ i,g i (r i)):= by
  intro i; rw [expand_eq];  change (∏ j,g j (i j))=_; conv_lhs => arg 2; intro k; rw [h k,expand_eq]
  let l j x:=if p x=i j then f j x else 0
  have ht j:Summable (l j):=(hf j).indicator (s:={x|p x=i j})
  rw [← (Cost.tsum_pi (f:=l) fun j=>summable_abs_iff.mpr (ht j)).2]; apply tsum_congr; intro u; split
  next h => exact prod_congr rfl (fun j _=> if_pos (congr_fun h j))
  next h =>
    obtain ⟨j,hj⟩:= Function.ne_iff.mp h; exact Finset.prod_eq_zero (mem_univ j) (if_neg hj)

variable (X) in
def prelude (i:Fin (n+1))(x:X): Locked X i x ≃ (Fin n→X) where
  toFun p:= i.removeNth p.val
  invFun p:=⟨i.insertNth x p,by simp⟩
  left_inv p:= Subtype.ext (Fin.insertNth_eq_iff.mpr ⟨p.property.symm,rfl⟩)
  right_inv p:= Fin.removeNth_insertNth ..
lemma prelude_at (i:Fin (n+1))(x:X) (w:Fin n→X): ((prelude X i x).symm w).val = i.insertNth x w:= rfl
lemma prelude_face (p:X→Y) (i:Fin (n+1))(x:X) (y:Fin n→X): (prelude Y i (p x)).symm (p∘y)= roll p i x ((prelude X i x).symm y):= by
  apply Subtype.ext; rw [prelude_at,Fin.insertNth_eq_iff]; exact ⟨(roll ..).2.symm, funext fun j=> by simp [roll,prelude_at,Fin.removeNth_apply]⟩

def ridge (X Y:Type*)(i:Fin (n+1))(y:Y): Locked Y i y × (Fin (n+1)→X) ≃ X × ( (Fin n→ X) × (Fin n→ Y)) where
  toFun p := (p.2 i,i.removeNth p.2,prelude _ i y p.1)
  invFun p := ((prelude _ i y).symm p.2.2, i.insertNth p.1 p.2.1)
  left_inv p:= Prod.ext ((prelude _ i y).symm_apply_apply _) (Fin.insertNth_self_removeNth i p.2)
  right_inv | ⟨x,a,b⟩=>Prod.ext (Fin.insertNth_apply_same (α:=fun _=>X) i x a) (Prod.ext (Fin.removeNth_insertNth i (α:=fun _=>X) x a) ((prelude _ i y).apply_symm_apply b))

section
variable {q:A→B}{l:Range X} {m:Range A}
variable {t:X→A→ℝ}{F:Field (Fin (n+1)) X}{H:Field (Fin (n+1)) Y}{G: Fin (n+1)→X→A→ℝ}{K:Fin (n+1)→Y→B→ℝ}
private def rays (G : Fin (n+1)→ X→ A→ℝ)(F:Field (Fin (n+1)) X) (i:Fin (n+1))(y:A)(p:X × ( (Fin n→ X) × (Fin n→ A))) : ℝ := G i p.1 y * (F (i.insertNth p.1 p.2.1)*(∏ j,G (i.succAbove j) (p.2.1 j) (p.2.2 j)))
private lemma reveals {i:Fin (n+1)}{y:A} (x:Locked A i y) (a: Fin (n+1) → X): F a *(∏ j,G j (a j) (x.val j))= rays G F i y (ridge X A i y (x,a)):= by
  unfold rays; dsimp only [ridge,prelude,Equiv.coe_fn_mk]; rw [Fin.prod_univ_succAbove (n:=n) (fun j=> G j (a j) (x.val j)) i,Fin.insertNth_self_removeNth,x.property]; unfold Fin.removeNth; ring
lemma basin {b c:Fin (n+1)→ℝ}{e:ℝ} (h:Shadow p F H)(hd:∀ i, Trails p q (G i) (K i))(hv:Rooted l F e)(hh:Ripple l m t)(hg:∀ i,Weirs t (G i) (b i) (c i)): Shadow q (allAt G F) (allAt K H) := by
  intro i x
  let P:= Prod.map p (Prod.map (fun y:Fin n→X=> p∘y) (fun y:Fin n→A=> q∘y))
  let Q:= Prod.map (roll q i x) (fun y:Fin (n+1)→X=>p∘ y)
  let R:= rays G F i x; let S:= rays K H i (q x)
  let u:=ridge X A i x; let v:=ridge Y B i (q x)
  have hu (y : Locked A i x × (Fin (n+1)→ X)): v (Q y) = P (u y) := Prod.ext rfl (Prod.ext (funext fun i=> rfl) (funext fun i=>rfl))
  let f (y : Locked A i x × (Fin (n+1)→ X)):= F y.2 * ∏ j,G j (y.2 j) (y.1.val j); let g (y : Locked B i (q x)× (Fin (n+1)→ Y)):= H y.2* ∏ j,K j (y.2 j) (y.1.val j)
  have hf : f=R ∘ u:= funext fun a=> reveals a.1 a.2; have he:g=S∘v:= funext fun a=> reveals a.1 a.2
  have hs : Summable f:= (budget_mono (laminar hv hh hg i x) (f:=fun y:Locked A i x × (Fin (n+1)→X) => ‖f y‖*m.bill y.1.val) (fun y=>norm_nonneg (f y)) (fun _=> le_mul_of_one_le_right (norm_nonneg _) (m.one_bill _))).2.1.of_norm
  let X' (x:X)(y:(Fin n → X) × (Fin n → A)):= F (i.insertNth x y.1) * ∏ j,G (i.succAbove j) (y.1 j) (y.2 j)
  let Y' (x:Y)(y:(Fin n → Y) × (Fin n → B)):= H (i.insertNth x y.1) * ∏ j,K (i.succAbove j) (y.1 j) (y.2 j)
  have hR (a:X):Scroll (Prod.map (fun y:Fin n→X=>p∘y) (fun y:Fin n→A=> q∘y)) (X' a) (Y' (p a)) := by
    have hj (j) (x:X) : SumBudget (fun y=> ‖G j x y‖) (c j):= budget_mono ((hg j).rows x) (fun _=>norm_nonneg _) (fun _=> le_mul_of_one_le_right (norm_nonneg _) (hh.one _ _))
    have hT:Summable (X' a):= by
       apply Summable.of_norm; simp_rw [X',norm_mul,norm_prod];
       have hA (y:Fin n→X):= budget_pi (fun j: Fin n=> hj (i.succAbove j) (y j)); exact (Cost.prod (g:=fun y:Fin n→X=> fun x:Fin n→A=> ∏ j, ‖G (i.succAbove j) (y j) (x j)‖) (budget_pull _ (prelude X i a).symm.injective (hv.raw i a)) hA (prod_nonneg fun j _=>(hg _).right)).2.1
    have hW:= (h i a).across (prelude X i a).symm (prelude Y i (p a)).symm (q:=fun y:Fin n→X=> p∘ y) (prelude_face p i a)
    have he (a:Fin n→X) : Scroll (fun y:Fin n→A=> q ∘ y) (fun x=>∏ j:Fin n,G (i.succAbove j) (a j) (x j)) (fun x=>∏ j:Fin n,K (i.succAbove j) (p (a j)) (x j)) := Scroll.pi (n:=n) (p:=q) (f:=fun j=>G (i.succAbove j) (a j)) (g:=fun j=> K (i.succAbove j) (p (a j))) (fun j=>(hj (i.succAbove j) _).2.1.of_norm) (fun j=>(hd _).row _)
    change Scroll (fun y:Fin n→X=>p ∘ y) (fun u:Fin n→X=>F (i.insertNth a u)) (fun v:Fin n→Y=>H (i.insertNth (p a) v)) at hW
    exact hW.chain (k:= fun y x=> ∏ j:Fin n,G (i.succAbove j) (y j) (x j)) (t:= fun y x=>∏ j:Fin n,K (i.succAbove j) (y j) (x j)) (q:=fun y:Fin n→A=> q ∘ y) he (show Summable (fun p:(Fin n → X) × (Fin n → A) => F (i.insertNth a p.1) * ∏ j, G (i.succAbove j) (p.1 j) (p.2 j)) from hT)
  have hS:Scroll P R S:= ((hd i).col x).chain (k:=X') (t:=Y') (q:=Prod.map (fun y:Fin n→X=>p∘y) (fun y:Fin n→A=> q∘y)) hR (show Summable R from u.summable_iff.mp (show Summable (R∘u) from hf ▸ hs))
  exact (show Scroll Q f g from he.symm ▸ hf.symm ▸ (hS.across u v hu)).collapse_fst hs
end
end YM.Pulse
