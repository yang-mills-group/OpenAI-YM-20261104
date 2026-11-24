import YM.FormalBulk08.Gorge.Couplet

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Gorge
open Lava Function Wick
open scoped BigOperators Classical ENNReal
variable {V : Type*} {σ : ℝ} {m n : ℕ} {D : Reach V} (q : V→V→ℝ)

lemma counted_rim {Q : (chain V m) → V→ ℝ≥0∞} {W : V→chain V n→ℝ≥0∞} (j : Fin n) (x : V) (L : V → V→ℝ≥0∞) (A B C : ℝ≥0∞)
   (he : (∑' v : pack j x,∑' b,W b v.val) ≤ B)
   (hh : ∀ a,(∑' t : chain V m,Q t a) ≤ A) (hr : ∀ b,(∑' a,L a b) ≤ C) :
   (∑' u : pack (Fin.natAdd m j) x,∑' i : V×V,Q (u.val ∘ Fin.castAdd n) i.1*W i.2 (u.val ∘ Fin.natAdd m)*L i.1 i.2) ≤ A*(B*C) := by
   -- mirror reduction
   let f : pack (Fin.natAdd m j) x → pack (Fin.castAdd m j) x:= fun v=>⟨Fin.append (v.val ∘ Fin.natAdd m) (v.val ∘ Fin.castAdd n),by simp [v.property]⟩
   have hf : Injective f := fun v w e=> Subtype.ext (funext fun k=> by
      have he:= congr_arg Subtype.val e; cases k using Fin.addCases with
      | left k=> simpa [f] using congr_fun he (Fin.natAdd n k)
      | right k=> simpa [f] using congr_fun he (Fin.castAdd m k))
   rw [mul_left_comm];
   let F (v : pack (Fin.castAdd m j) x) := ∑' i: V × V,W i.1 (v.val ∘ Fin.castAdd m)*Q (v.val ∘ Fin.natAdd n) i.2 * L i.2 i.1
   have ht : (∑' v,F v) ≤ _ := counted_cast (Q:=fun w b=>W b w) (W:=fun a w=>Q w a) j x (fun b a=> L a b) B A C he hh hr
   refine le_trans ?_ ((ENNReal.tsum_comp_le_tsum_of_injective hf F).trans ht)
   apply le_of_eq; refine tsum_congr fun u=> ?_; unfold F; rw [← Equiv.tsum_eq (Equiv.prodComm V V) (fun i: V×V=> Q (u.val ∘ Fin.castAdd n) i.1*W i.2 (u.val ∘ Fin.natAdd m)*L i.1 i.2)]; simp [f,Function.comp_def, mul_comm]

lemma logs_attach {r : ℕ} {T : Tile V (r+1)} {C : ℝ} (h : Bail D σ T C) (i : Fin r) (x:V) :
     (∑' v : pack i x, ∑' a, glitter D σ T (Fin.cons a v.val)) ≤ ENNReal.ofReal C := by
   let f : pack i x × V → pack i.succ x := fun u=> ⟨Fin.cons u.2 u.1.val,by simp [u.1.property]⟩
   rw [← ENNReal.tsum_prod]; refine h.watch f ?_; rintro ⟨v,a⟩ ⟨w,b⟩ e
   have he:=congr_arg Subtype.val e; simp [f,Fin.cons_inj] at he; simp [he.1,Subtype.ext he.2]
lemma rim_stud {r : ℕ} {T : Tile V (r+1)} {C : ℝ} (h : Bail D σ T C) (x:V) :
     (∑' v : chain V r, glitter D σ T (Fin.cons x v)) ≤ ENNReal.ofReal C := by
   let f : chain V r → pack (0:Fin (r+1)) x:= fun v=> ⟨Fin.cons x v,by simp⟩
   exact h.watch f fun v w e=> by simpa [f,Fin.cons_inj] using congr_arg Subtype.val e
lemma toss_bond {T : Tile V (m+1)} {S : Tile V (n+1)} {B C A : ℝ} (hs : 0≤σ) (h : Bail D σ T A) (e : Bail D σ S B) (he : Grate D σ q C) (hv : Grate D σ (fun i j=>q j i) C) :
    Fling D σ (weld q T S) ((1/2*(m+1)*(n+1))*(A*(B*C))) := by
   have hM : 0 ≤ B*C:=mul_nonneg e.1 he.1;have hN : 0 ≤ (1:ℝ)/2*(m+1)*(n+1):=by positivity
   refine ⟨mul_nonneg hN (mul_nonneg h.1 hM),fun i a=> ?_⟩
   refine le_trans (ENNReal.tsum_le_tsum fun v=> ENNReal.tsum_le_tsum fun k=> joint_pay D q T S v.val k hs) ?_
   simp_rw [ENNReal.tsum_mul_left,ENNReal.ofReal_mul hN,ENNReal.ofReal_mul h.1, ENNReal.ofReal_mul e.1]
   gcongr
   cases i using Fin.addCases with
   | left i=> exact counted_cast (Q:=fun w x=>glitter D σ T (Fin.cons x w)) (W:=fun x w=>glitter D σ S (Fin.cons x w)) i a (fun x y=>shine σ (D.d x y)* ‖q x y‖ₑ) _ _ _ (logs_attach h i a) (rim_stud e) he.2
   | right j=> exact counted_rim (Q:=fun w x=>glitter D σ T (Fin.cons x w)) (W:=fun x w=>glitter D σ S (Fin.cons x w)) j a (fun x y=>shine σ (D.d x y)* ‖q x y‖ₑ) _ _ _ (logs_attach e j a) (rim_stud h) (fun b=>by simpa only [D.turn b] using hv.2 b)
lemma Bail.bond {T : Tile V (m+1)} {S : Tile V (n+1)} {B C A : ℝ} (hs : 0≤σ) (h : Bail D σ T A) (e : Bail D σ S B) (he : Grate D σ q C) (s : ∀ i j,q i j=q j i) :
      Bail D σ (Lava.bond q T S) ((1/2*(m+1)*(n+1))*(A*(B*C))) := (toss_bond q hs h e he (he.turn s)).bail
end YM.FormalBulk08.Gorge
