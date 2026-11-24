import YM.FormalBulk08.Gorge.Beacon

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Gorge
open Lava Function Wick
open scoped BigOperators Classical ENNReal
variable {V I : Type*} {σ τ : ℝ} {r : ℕ} {D : Reach V} {R : Reach I}

structure Solar (D : Reach V) (R : Reach I) (σ τ : ℝ) where
   capsule : V → I → ℝ≥0∞
   fare : ℝ
   good : 0≤fare
   carried : ∀ {r : ℕ} (w : chain V r) (v : chain I r), shine τ (wide R v) ≤ ENNReal.ofReal fare * shine σ (wide D w) * ∏ i,capsule (w i) (v i)

structure Hill (L : V → I → ℝ≥0∞) (M : V→I→ℝ) (B C : ℝ) : Prop where
   costs : 0≤B
   money : 0≤C
   rows : ∀ x,(∑' y,L x y*‖M x y‖ₑ)≤ ENNReal.ofReal B
   columns : ∀ y,(∑' x,L x y*‖M x y‖ₑ)≤ ENNReal.ofReal C
lemma Hill.mono {L : V → I → ℝ≥0∞} {M : V→I→ℝ} {B C B' C' : ℝ} (h : Hill L M B C) (e : B≤ B') (f : C≤ C') : Hill L M B' C' := ⟨h.costs.trans e,h.money.trans f,fun x=>(h.rows x).trans (ENNReal.ofReal_le_ofReal e), fun y=>(h.columns y).trans (ENNReal.ofReal_le_ofReal f)⟩

lemma lamp_counts (T : Tile V r) (M : Fin r → V→ I→ℝ) (L : Solar D R σ τ) (A : ℝ) (B C : Fin r→ℝ) (i : Fin r) (a : I)
    (h : Bail D σ T A) (H : ∀ i,Hill L.capsule (M i) (B i) (C i)) :
    (∑' v: pack i a,∑' w, shine τ (wide R v.val) * ‖T w*∏ j, M j (w j) (v.val j)‖ₑ) ≤ ENNReal.ofReal L.fare * (ENNReal.ofReal A * ENNReal.ofReal (C i)* ∏ j∈Finset.univ.erase i,ENNReal.ofReal (B j)) := by
   let W (j) (x) (y) := L.capsule x y* ‖M j x y‖ₑ
   have ht := towline (glitter D σ T) a i (fun y x=>W i x y) W (fun w _ j=> w j) (ENNReal.ofReal A) _ (fun j=> ENNReal.ofReal (B j)) (h.2 i) ((H i).columns a) (fun j _ v _=>(H j).rows (v j))
   refine le_trans ?_ (mul_le_mul_right ht (ENNReal.ofReal L.fare));
   rw [←ENNReal.tsum_mul_left];refine ENNReal.tsum_le_tsum fun v=>?_; rw [← ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun w=> ?_
   refine (mul_le_mul_left (L.carried w v.val) _).trans (le_of_eq ?_); rw [show W i (w i) a = W i (w i) (v.val i) by rw [v.property]]
   have enorm_prod (S : Finset (Fin r)) (x : Fin r→ℝ) : ‖∏ j∈S,x j‖ₑ=∏ j∈S, ‖x j‖ₑ:= by induction S using Finset.induction <;> simp_all [enorm_mul]
   rw [enorm_mul,enorm_prod]; unfold glitter; calc
      _ = ENNReal.ofReal L.fare*(shine σ (wide D w)* ‖T w‖ₑ)*(∏ j:Fin r,W j (w j) (v.val j)) := by unfold W; rw [Finset.prod_mul_distrib];ring
      _ = _ := by rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]; ring
lemma toss_pearl {T : Tile V r} (M : V→I→ℝ) (L : Solar D R σ τ) (A B C : ℝ) (h : Bail D σ T A) (H : Hill L.capsule M B C) :
    Fling R τ (fun v w=> T w * ∏ i, M (w i) (v i)) (L.fare*(A*C*B^(r-1))) := by
   refine ⟨mul_nonneg L.good (mul_nonneg (mul_nonneg h.1 H.money) (pow_nonneg H.costs _)),fun i a=> ?_⟩
   rw [ENNReal.ofReal_mul L.good,ENNReal.ofReal_mul (mul_nonneg h.1 H.money),ENNReal.ofReal_mul h.1,ENNReal.ofReal_pow H.costs]
   simpa only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,Fintype.card_fin] using lamp_counts T (fun _=>M) L A (fun _=>B) (fun _=>C) i a h (fun _=>H)

lemma Bail.pearl {T : Tile V r} {M : V→I→ℝ} {A B C : ℝ} (L : Solar D R σ τ) (h : Bail D σ T A) (H : Hill L.capsule M B C) :
    Bail R τ (pearl M T) (L.fare*(A*C*B^(r-1))) := (toss_pearl M L A B C h H).bail
end YM.FormalBulk08.Gorge
