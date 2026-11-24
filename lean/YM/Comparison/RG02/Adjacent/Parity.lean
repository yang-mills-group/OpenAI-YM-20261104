import YM.Comparison.RG02.Adjacent.Barter
/-!
# Deterministic ranked parity and signs preserved at reset
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
local notation "φ"=> 𝓝 (0:ℝ)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
namespace Preserves
variable {K:UnitCost} (d:ℤ) {p:Display X} {α:ℂ}
lemma motneg {f:ℝ→ℂ} (h:ContDiffAt ℝ ω f 0) (i:ℕ) : motion (fun t=> f (-t)) i=(-1:ℂ)^i *motion f i:= by
   let P:ℝ→L[ℝ]ℝ:= -ContinuousLinearMap.id ℝ _
   have hp:P 1=(-1:ℝ) • 1:= by simp [P]
   rw [show motion (fun t=> f (-t)) i= _ from Assembly.jet_continuous_right P (h.of_le le_top) 1,hp, Clipper.weight,Complex.real_smul]; push_cast; rfl
lemma oddblank {f:ℝ→ℂ}(h:ContDiffAt ℝ ω f 0)(hp:∀ᶠ t in φ,f (-t)=f t)(i:ℕ)(hi:Odd i): motion f i=0:= by
   have he:= (motneg h i).symm.trans (mgerm hp); rw [hi.neg_one_pow,neg_one_mul] at he; exact neg_eq_self.mp he
lemma oddPrice (hk: K.Even) {i j k:ℕ}(he:j ≤ i)(hv: Odd (i-j)): motion (money K d j k) i=0:= by
   rw [triangular,if_pos he]; exact oddblank (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (checks K d j k)) (hk.mono fun t ht=>by simp only [Function.comp_apply,ht]) _ hv
-- direct transfer evaluation
variable {r:ℕ}
def Weight (p:Display X)(r:ℕ)(y:ℂ): Prop:= ∀i≤r,∀ x,p i (-x)= y*(-1)^i*p i x
lemma retained (hK:K.Even)(h:Weight p r α)(hp:∀ i≤r,ContDiff ℝ ω (p i)): Weight (born p K d r) r α:= by
   intro i hi x; let f(t:ℝ):= ages p d r t (K.rating t) x
   have hf: ContDiffAt ℝ ω f 0:= by unfold f ages cover; refine (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (K.spin d)).mul (ContDiffAt.sum fun j hj =>?_); exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ K.here).pow _).mul ((hp j (mem_range_succ_iff.mp hj)).contDiffAt.comp (0:ℝ) ((K.smooth.inv (by simp [K.origin])).smul contDiffAt_const))
   have he : (fun t:ℝ=> ages p d r t (K.rating t) (-x))=ᶠ[φ]fun t=>α*f (-t):= by
      filter_upwards [hK] with t ht; unfold f ages cover; rw [ht]; simp_rw [smul_neg,mul_sum]
      apply sum_congr rfl; intro j hj; rw [h j (mem_range_succ_iff.mp hj)]; -- lhs *(α (-1)^j ...)
      push_cast; rw [neg_mul,neg_pow ((t:ℂ)*(K.rating t:ℂ))]; ring
   have hg: ContDiffAt ℝ ω (fun t:ℝ=> f (-t)) 0:= by
      let P:ℝ→L[ℝ] ℝ:= -ContinuousLinearMap.id ℝ _; exact (P.map_zero.symm ▸ (show ContDiffAt ℝ ω f 0 from hf) : ContDiffAt ℝ ω f (P 0)).comp _ P.contDiff.contDiffAt
   unfold born; rw [mgerm he]; exact (mscale α hg).trans (by rw [show motion _ i=(-1)^i*motion f i from motneg hf _, ← mul_assoc])

lemma motion_real {f:ℝ→ℂ}(h:ContDiffAt ℝ ω f 0)(hp:∀ᶠ x in φ,Rim (f x))(k:ℕ): Rim (motion f k):= by
   let g:ℝ→ℝ := Complex.reCLM ∘ f; have h':ContDiffAt ℝ ω g 0:= Complex.reCLM.contDiff.contDiffAt.comp _ h
   refine ⟨Assembly.jet g k 1,(mgerm (g:=Complex.ofRealCLM ∘ g) (hp.mono fun x hx=> hx.re.symm)).trans (Assembly.jet_apply_left Complex.ofRealCLM g k (h'.of_le le_top) 1).symm⟩
lemma stays (K:UnitCost)(hp:∀ i≤r,ContDiff ℝ ω (p i))(h:∀ i≤r,∀x,Rim (p i x))(i:ℕ)(x:X): Rim (born p K d r i x):= by
   let f(t:ℝ):= ages p d r t (K.rating t) x; have hf: ContDiffAt ℝ ω f 0:= by unfold f ages cover; refine (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (K.spin d)).mul (ContDiffAt.sum fun j hj =>?_); exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ K.here).pow _).mul ((hp j (mem_range_succ_iff.mp hj)).contDiffAt.comp (0:ℝ) ((K.smooth.inv (by simp [K.origin])).smul contDiffAt_const))
   exact motion_real hf (Eventually.of_forall fun u=> (Rim.ofReal _).mul (Rim.sum (range (r+1)) fun j hj=> ((Rim.ofReal _).pow _).mul (h j (mem_range_succ_iff.mp hj) _))) i
end Preserves
end YM.Comparison.RG02.Adjacent
