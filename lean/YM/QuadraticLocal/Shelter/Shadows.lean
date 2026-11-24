import YM.QuadraticLocal.Tint.Alcove
/-!
# Pack, negate, and partition log families

Use on same supports, not any moment-equivalent family. Only split by
exact lamps and operations; splitting masked logs needs inputs still paid.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Lamps
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n:Side}{V α ι μ κ : Type*}[DecidableEq V] {R:Census V}{o:V→Site n}{P:BudgetPoint}
variable (L:Lamps α ι G P o R)(w: V→ℝ) {b c d:ℝ} {B:ℕ}
def shade : Lamps α ι G P o R where
 mode:=L.mode
 live:=L.live
 address:=L.address
 roots:=L.roots
 nominal:= fun t i=> -(L.nominal t i)
 legal t i:= by simpa using regular_smul (-1) (L.legal t i)
 clear:=L.clear
 pure t i U h:= congr_arg (- ·) (L.pure t i U h)
lemma expenseShade (h:L.Paid w B b c):(shade L).Paid w B b c:=by
    obtain ⟨f,hF,hC,hH⟩:=h.budget; refine ⟨f,hF,fun i t u hu=>?_,hH⟩
    change P.supBounds u (L.ground i) (-L.nominal t i) (f i)
    simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using bound_smul (c:=(-1)) (hC i t u hu)
lemma shade_frame (t:α)(v:Config G n) (i:ι) : (L.shade).frame i t v= - L.frame i t v:=by
    unfold Lamps.frame shade; have he s (x:ℂ) : @Poly.send _ _ R s (-x)=-Poly.send s x:=by ext; simp only [Poly.part_send,Poly.part_neg];split <;> simp
    unfold Lamps.light; dsimp only [ground]; split_ifs; exact he _ _; rw [←he]; congr
    by_cases hh:Healthy P.threshold (L.address i).support v; rw [masked_eq _ _ _ _ hh,masked_eq _ _ _ _ hh]; rfl; rw [masked_ne _ _ _ _ hh,masked_ne _ _ _ _ hh,neg_zero]
lemma shade_log(t:α)(v:Config G n): L.shade.log t v=-L.log t v:=by unfold Lamps.log;simp_rw [shade_frame]; exact tsum_neg ..
lemma separate (p: μ⊕κ≃ι) (f:μ→ι) (g:κ→ι) (hf:∀ j,p (.inl j)=f j)(hg:∀ i,p (.inr i)=g i) (t:α)(v:Config G n)(hs:Summable (fun i=> L.frame i t v)) : L.log t v= (L.summon f).log t v+(L.summon g).log t v:=by
   let F i:=L.frame i t v; have ht:HasSum (F ∘ p) (L.log t v):= p.hasSum_iff.mpr hs.hasSum
   unfold log at *; simp_rw [summonFrame]; rw [←funext (f:=p ∘ Sum.inl) hf,←funext (f:=p ∘ Sum.inr) hg]; exact ht.unique (HasSum.sum (ht.summable.comp_injective Sum.inl_injective).hasSum (ht.summable.comp_injective Sum.inr_injective).hasSum)
lemma inlPaid (A:Lamps α μ G P o R) (h:(L.join A).Paid w B b c):L.Paid w B b c:= (L.join A).summonPaid w Sum.inl Sum.inl_injective h
lemma inrPaid (A:Lamps α μ G P o R)(h:(L.join A).Paid w B b c):A.Paid w B b c:= (L.join A).summonPaid w Sum.inr Sum.inr_injective h
lemma tenure (ht:∀ i,0< w i)(h:L.Paid w B b c)(he:d≤b) : L.Paid w B d c:=by obtain ⟨f,hf,hH,hF⟩:=h.budget; refine ⟨f,hf,hH,fun i=>budget_mono (hF i) (fun j=>by split; exact mul_nonneg (mul_nonneg (Poly.worth ht _).le (hf _)) (Real.exp_nonneg _); rfl) (fun j=>by split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (by positivity))) (mul_nonneg (Poly.worth ht _).le (hf _)); rfl)⟩
end YM.QuadraticLocal.Lamps
