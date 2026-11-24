import YM.RegulatorIR.Epoch.Phase

/-! Two-way without repeated cost. Used additive β marginal frame costs.
Choice depends on W but alignment is phase exact. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Epoch
open Function Set Finset Filter YM.RegulatorIR.Ledger Uniform ENNReal
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X:Type}{M:X→ℕ}{k:ℕ}{u v:ℝ}
namespace Marked
variable (S:Marked M)

lemma back_money (D:Choice M)(f:Page M→ℝ≥0∞)(F:Page M→ℝ≥0∞)(p:ℕ)(c:ℝ≥0∞)(hb:∀ w,S.peak (D.choose w)=0)(hF : Balancer D F)
 (h:∀ w,f (D.choose w)=0) (hf:∀ w:Flap M,backward D w.next→ f w.prev≤ f w.next + c*S.age_f.val w^p*F w.prev) : ∀ i,backward D i→ f i≤ ruff D i * (c*S.age_t.val i^p)*F i :=by
 refine clip_back D ?_ ?_
 · intro w; rw [h];exact bot_le
 rintro w ht hv;
 have he:backward D w.prev:= (show w.prev.downW ≤ w.next.downW from Nat.le_succ _) |>.trans ht
 have hV: ruff D w.prev=ruff D w.next+1:=by rw [ruff_b D _ he,ruff_b D _ ht]; exact_mod_cast (show D.age w.volW - w.offset=D.age w.volW-(w.offset+1)+1 from by change w.offset+1≤ D.age w.volW at ht;omega)
 have H : S.age_t.val w.next ≤ S.age_t.val w.prev:=by
    apply ENNReal.ofReal_le_ofReal; unfold credit; rw [abs_of_nonpos (S.debit D hb _ ht), abs_of_nonpos (S.debit D hb _ he)]
    apply add_le_add_right;rw [S.mark_P]; exact neg_le_neg (le_add_of_nonneg_right (S.rise w).le)
 apply (hf w ht).trans ((add_le_add_left hv _).trans ?_)
 rw [hV,add_mul,add_mul,one_mul]; exact add_le_add_left (mul_le_mul' (mul_le_mul_right (mul_le_mul_right (pow_le_pow_left' H _) _) _) (hF.before w ht)) _

lemma front_money (D:Choice M)(f:Page M→ℝ≥0∞)(F:Page M→ℝ≥0∞)(p:ℕ)(c:ℝ≥0∞)(hb:∀ w,S.peak (D.choose w)=0)(hF : Balancer D F)
 (h:∀ w,f (D.choose w)=0) (hf:∀ w:Flap M,forward D w.prev→ f w.next≤ f w.prev + c*S.age_f.val w^p*F w.prev) : ∀ i,forward D i→ f i≤ ruff D i * (c*S.age_t.val i^p)*F i :=by
 refine clip_fore D ?_ ?_
 · intro w; rw [h];exact bot_le
 rintro w ht hv;
 have he:forward D w.next:= le_trans ht (show w.prev.downW≤w.next.downW from Nat.le_succ _)
 have hV: ruff D w.next=ruff D w.prev+1:=by rw [ruff_c D _ he,ruff_c D _ ht]; exact_mod_cast (show w.offset+1-D.age w.volW=w.offset-D.age w.volW+1 from by change D.age w.volW≤w.offset at ht;omega)
 have H : S.age_t.val w.prev ≤ S.age_t.val w.next:=by
    apply ENNReal.ofReal_le_ofReal; unfold credit; rw [abs_of_nonneg (S.credit_p D hb _ ht), abs_of_nonneg (S.credit_p D hb _ he)]
    apply add_le_add_right;rw [S.mark_P]; exact le_add_of_nonneg_right (S.rise w).le
 apply (hf w ht).trans ((add_le_add_left hv _).trans ?_)
 have hh:= mul_le_mul_right (pow_le_pow_left' H p) c
 rw [hV,add_mul,add_mul,one_mul]; exact add_le_add (mul_le_mul' (mul_le_mul_right hh _) (hF.after w ht)) (mul_le_mul' hh (hF.after w ht))

lemma license (D:Choice M)(f:Page M→ℝ)(F:Page M→ℝ≥0∞)(hb:∀ w,S.peak (D.choose w)=0)(hF : Balancer D F)
 (H:∀ w,f (D.choose w)=0)(ht:Carry S.age_f (F ∘ Flap.prev) fun w:Flap M=> ‖f w.next-f w.prev‖ₑ): Carry S.age_t F fun p=> ‖f p‖ₑ:=by
 obtain ⟨c,⟨B,p,hb',h⟩,hz⟩:=ht
 let g i:=‖f i‖ₑ; have he(i:X):g (D.choose i)=0:=by simp [g,H]
 refine ⟨_, (S.ruff_size D hb).mul ((Poly.standard _ hb').mul ((Poly.roof _).powQ p)),?_⟩
 have hv(w:Flap M): ‖f w.next-f w.prev‖ₑ≤ B*S.age_f.val w ^p*F w.prev:=(hz w).trans (mul_le_mul_left (h w) _)
 intro i; by_cases hy:backward D i
 · refine S.back_money D g F p B hb hF he (fun w _=>?_) i hy
   calc
      _ = ‖f w.next+ -(f w.next-f w.prev)‖ₑ:=by unfold g; rw [show f w.next+_= f w.prev by abel]
      _ ≤ _:= (enorm_add_le ..).trans (add_le_add_right ((enorm_neg _).trans_le (hv w)) _)
 refine S.front_money D g F p B hb hF he (fun w _=>?_) i (le_of_lt (lt_of_not_ge hy))
 calc
    _ = ‖f w.prev + (f w.next-f w.prev)‖ₑ:=by unfold g; rw [show f w.prev+_=f w.next by abel]
    _ ≤ _:= (enorm_add_le ..).trans (add_le_add_right (hv w) _)
end Marked
end YM.RegulatorIR.Epoch
