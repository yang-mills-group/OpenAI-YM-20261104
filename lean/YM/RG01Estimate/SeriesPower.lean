import YM.RG01Estimate.Series
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Series
open Function Filter Set Metric Finset MeasureTheory
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {X E Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n k m l r : ℕ} {b u v t : ℝ} {z : X}
lemma Hon.shift {f g : X → E}{x y:Policy X E} (h : Hon b r n x f u z)(hx:g =ᶠ[𝓝 z] f)(he:∀ i<r, y i=ᶠ[𝓝 z] x i) : Hon b r n y g u z:= by
    refine ⟨h.positive,fun i hi=>(h.present i hi).shimmy (he i hi), h.priced.shimmy ?_⟩
    filter_upwards [hx,(Finset.eventually_all (Finset.range r)).2 fun i hi=> he i (mem_range.mp hi)] with i hi hi'
    refine congr_arg₂ (·-·) hi (Finset.sum_congr rfl (fun j hj=> congr_arg ((b^j) • ·) (hi' _ hj)))
lemma Hon.zero : Hon b r n (fun (_:ℕ) (_:X) => (0:E)) (fun _=>0) 0 z:= by
    refine ⟨le_refl _,fun _ _=>?_,?_⟩
    · simpa only [norm_zero] using! Brush.certified (F:=E) (k:=n) (x:=z) zero_le_one 0
    unfold trunc; simp only [smul_zero,sum_const_zero,sub_zero,mul_zero]
    simpa only [norm_zero] using! Brush.certified (F:=E) (k:=n) (x:=z) zero_le_one 0
lemma Hon.constant (f:E)(hp:0<r): Hon b r n (fun i _=> if i=0 then f else 0) (fun _=> f) ‖f‖ z:= by
    let M i (_:X):=if (i:ℕ)=0 then f else 0
    refine ⟨norm_nonneg _,fun i hi=>?_,?_⟩
    · by_cases hi:i=0
      · rw [hi, if_pos rfl]; exact Brush.certified zero_le_one _
      rw [if_neg hi]; exact (Brush.certified zero_le_one _).climb (by rw [norm_zero]; exact norm_nonneg _) le_rfl
    have hm (x:X):trunc M b r x=f:= by
       unfold trunc; rw [Finset.sum_eq_single 0]
       · simp [M]
       · intro i hi hv; simp [M,hv]
       intro h; exact False.elim (h (mem_range.mpr hp))
    exact (((Brush.certified (k:=n) zero_le_one (x:=z) (0:E)).climb (show ‖(0:E)‖≤ |b|^r*‖f‖ from by rw [norm_zero]; positivity) le_rfl).shimmy (g:= fun x=> f-trunc M b r x) (Eventually.of_forall fun x=> by simp only [hm x,sub_self]))
lemma Hon.sum_pol {ι:Type} (s:Finset ι) {f : ι→ X→ E}{C:ι→ ℝ}{p:ι→ Policy X E}(hp : ∀ i∈ s, Hon b r n (p i) (f i) (C i) z) : Hon b r n (fun i x=> ∑ j∈ s,p j i x) (fun x=>∑ i∈s,f i x) (∑ i∈s,C i) z:= by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Hon.zero
    | insert i s hi H=>
       have hf := hp i (mem_insert_self i s); have hs := H (fun j hj=>hp j (mem_insert_of_mem hj)); simp_rw [sum_insert hi]; exact hf.more hs
section multiplicative
variable (L : Y →L[ℝ] E →L[ℝ] E) (x:X)
def mulPow (M:Policy X ℝ) (n : ℕ) : Policy X ℝ:= Nat.rec
    (fun j _=> if j=0 then 1 else 0) (fun _ f i k=> convolve (ContinuousLinearMap.mul ℝ ℝ) f M i k) n
def pricedPow (k n r:ℕ)(u:ℝ) := Nat.rec (motive:=fun _=>ℝ) 1 (fun _ f=> addition n r 1 f u) k
lemma Hon.powers {f:X→ℝ}{M : Policy X ℝ}(p: Hon b r n M f u z) (hx:0<r)(hb:|b|≤1)(i:ℕ): Hon b r n (mulPow M i) (fun x=> f x^i) (pricedPow i n r u) z:= by
    induction i with
    | zero=>
       simp only [pow_zero]; have h:=constant (X:=X) (z:=z) (b:=b) (n:=n) (1:ℝ) hx; rw [norm_one] at h; exact h
    | succ i ih=> simp_rw [pow_succ]; exact ih.twins p _ hb (ContinuousLinearMap.opNorm_mul_le ..)
lemma Hon.closed {f:X→E} {x: Policy X E} (p: Hon b r n x f u z) (h:0<r)(hb:|b|≤1)(he:x 0=ᶠ[𝓝 z] 0): Brush n ((r*u+u)*|b|) 1 f z:= by
    have heq: (r:ℝ)*u*(|b|)=∑ i∈Finset.range r, (fun _:_=> |b| *u) i:= by simp; ring
    have hp : Brush n (r*u*|b|) 1 (trunc x b r) z:= by
       unfold trunc; rw [heq]
       apply Brush.spree _ _ _ zero_le_one; intro i hi
       by_cases hx:i=0
       · subst i; exact (((Brush.certified (k:=n) zero_le_one (0:E)).climb (by rw [norm_zero]; exact mul_nonneg (abs_nonneg _) p.positive) le_rfl).shimmy (he.mono fun y hy=> by change b^ (0:ℕ) • x 0 y=0; simp only [pow_zero,one_smul]; exact hy))
       refine ((p.present i (mem_range.mp hi)).smul (b^i)).climb (mul_le_mul_of_nonneg_right ?_ p.positive) le_rfl
       rw [Real.norm_eq_abs,abs_pow]
       exact (pow_le_pow_of_le_one (abs_nonneg _) hb (show 1≤ i by omega)).trans_eq (pow_one _)
    have hf := (p.priced.climb (mul_le_mul_of_nonneg_right ((pow_le_pow_of_le_one (abs_nonneg _) hb (show 1≤r from h)).trans_eq (pow_one _)) p.positive) le_rfl).gathering hp
    refine (hf.climb (le_of_eq ?_) le_rfl).shimmy (Eventually.of_forall fun i=> (sub_add_cancel _ _).symm); ring
end multiplicative
open Laplace Lattice
variable {G:Gauge}{P:Side}
lemma paid_mul (n r:ℕ) {f g:ℝ→ℝ} {c:ℝ} (hp:Cookie G P f)(h:Cookie G P g) : Cookie G P (fun x=> addition n r c (f x) (g x)):= by
    have hc {f g:ℝ→ℝ} (p:Cookie G P f)(q:Cookie G P g): Cookie G P (fun x=> Series.cost n c (f x) (g x)):= ((Cookie.const _).pays (p.pays q)).pays (Cookie.const _)
    let ht:= hc hp h; let W:= Cookie.const (G:=G) (L:=P) (r:ℝ)
    exact (W.pays ht).joins (((hc hp (h.joins (W.pays h))).joins (hc (W.pays hp) h)).joins (W.pays (W.pays ht)))
lemma paid_pow {f:ℝ→ℝ}(p:Cookie G P f)(k n r:ℕ): Cookie G P (fun x=> pricedPow k n r (f x)):= by
    induction k with
    | zero=> exact Cookie.const _
    | succ i ih=> exact paid_mul _ _ ih p
end YM.RG01Estimate.Series
