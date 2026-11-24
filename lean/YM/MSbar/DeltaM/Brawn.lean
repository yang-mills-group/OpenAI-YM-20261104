import YM.MSbar.DeltaM.Toll
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar MvPolynomial Analysis Bakery Lattice
variable {ι σ τ:Type}[Fintype ι][Fintype τ][Fintype σ][DecidableEq ι][DecidableEq τ][DecidableEq σ]{X: Type*}[MeasurableSpace X]{μ:Measure X}[IsProbabilityMeasure μ]
variable {n:Side}{k q:ℕ}{f:X→ View σ}{g:X→ View σ}{ξ: View σ→ℝ}{l:σ→ Site n}{p ε t v r a c u ℓ:ℝ}{z:Site n}
structure FetchD (l:σ→ Site n)(t v:ℝ)(f:View σ→ℝ) :Prop where
    whole : Canopy f
    smooth x : ContDiffAt ℝ 2 f x
    nonnegative:0≤ v
    tilt i x:|glance f [i] x| ≤ v
    rises i :∃ h:σ→ℝ, (∀ x j, |glance f [i,j] x|≤ h j) ∧ ∑ j, h j * Eve t (l i) (l j) ≤ v
-- h weighted.Orthonormal from tape.Lp.χ.D.Can choose supplied.S whole.Frame.Light.App consumer.
namespace FetchD
variable (K:FetchD l t v ξ)
include K
lemma wind (i:σ)(hm:Measurable f)(k:ℕ): Bank μ k (fun j=> glance ξ [i] (f j)) v:= Bank.fixed ((curtain i K.whole|>.measurable).comp hm) (fun _=>K.tilt i _) K.nonnegative
lemma delta (hp:∀ i:σ,Bank μ k (fun x=> f x i-g x i) (p* Eve t z (l i))) (i:σ) (ht:0≤p)(ha:0≤ t) (hf:Measurable f)(hg: Measurable g): Bank μ k (fun j=> glance ξ [i] (f j)-glance ξ [i] (g j)) (p*Eve t z (l i)*v):=by
    obtain ⟨h,H,He⟩:=K.rises i; let s (j:σ):= p* Eve t z (l j); let y(j:σ)(x) := f x j -g x j; have hy(j): 0 ≤ h j:= (abs_nonneg _).trans (H 0 j); let Φ(x):=∑ j:σ, |y j x| *h j
    have hp(j): Bank μ k (fun x=> (|y j x|)*h j) (h j *s j):=by
          let g(j:σ):=Bank.normed (hp j) (g:=fun x=> |y j x|) ((hp j).meas.abs) (fun i=>by rw [abs_abs])
          rw [show (fun x=> |y j x| *h j)=_ from (show (fun x=> _)=_ from funext fun x=>mul_comm (|y j x|) (h j))]; have hj :=(g j|>.falls (h j)); rw [abs_of_nonneg (hy j)] at hj; exact hj -- bad ▸
    letI :MeasurableSpace σ := ⊤ -- for Bank.mcast needs
    have hΦ: Bank μ k Φ (p* Eve t z (l i)*v):= Bank.length (u:=p* Eve t z (l i)*v) (Bank.mcast (μ:=μ) (Finset.univ:Finset σ) _ _ (fun j _=>hp j)) ?_
    · apply Bank.normed hΦ (((curtain i K.whole).measurable.comp hf).sub ((curtain i K.whole).measurable.comp hg)); intro x
      obtain ⟨y',-,hY⟩:= cutAt (f:=ξ) (X:=Set.univ) [i] (convex_univ) (Set.mem_univ (g x)) (Set.mem_univ (f x)) (fun x _=>K.smooth x); change |glance ξ [i] (f x)-glance ξ [i] (g x)|≤ _; rw [hY]; refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun j _=>?_)).trans (le_abs_self (Φ x))); exact (abs_mul ..).trans_le (mul_le_mul_of_nonneg_left (H y' j) (abs_nonneg _))
    · apply le_trans _ (mul_le_mul_of_nonneg_left He (mul_nonneg ht (Real.exp_pos _).le)); rw [mul_sum]; apply sum_le_sum; intro x hx; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (eve_t ha z (l i) (l x)) ht) (hy x)).trans_eq; unfold Eve; ring
variable {v1 w d :ℝ}{q':Finset σ}{m:ℕ}
lemma solar (hp:∀ i:σ,Bank μ (m+1) (fun x=> f x i-g x i) (p*Eve t z (l i))) (H₀:∀ i∈ q', Eve t z (l i) ≤ c) (i:σ) (ht:0≤p)(ha:0≤t)(hx:0 ≤ c)(hf:Measurable f)(hg:Measurable g)(hf':∀ i∈q',Bank μ (m+1) (fun x => f x i) w)(hg':∀ i∈q',Bank μ (m+1) (fun x=>g x i) w)(hK: 1≤w) (L:List σ)(hL:L.toFinset⊆q')(hm:L.length≤m):
    let A(v:X→View σ) := (∫ x,glance ξ [i] (v x)*eval (v x) (play L) ∂μ)
    |A f| ≤ v*w^m ∧ |A g| ≤ v*w^m ∧ |A f-A g| ≤ (p*v * (1+m*c) *w^m)*Eve t z (l i) :=by
    have ht :1+L.length≤m+1:=by omega
    have hx' :=K.nonnegative; let V':= L.length;let z' := Eve t z (l i); have hΩ :1 ≤ z':=Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _));
    obtain ⟨hX,hY,hZ⟩:= reproduce f g 1 L (zero_le_one.trans hK) (mul_nonneg ‹0 ≤ p› hx) (fun i hi=>⟨(hf' i (hL (List.mem_toFinset.mpr hi))).slips ht,(hg' i (hL (List.mem_toFinset.mpr hi))).slips ht,(hp i|>.slips ht|>.length (mul_le_mul_of_nonneg_left (H₀ i (hL (List.mem_toFinset.mpr hi))) ‹0 ≤ p›))⟩) -- diff p*c
    let X₀(v : X→View σ)(x):= glance ξ [i] (v x)*eval (v x) (play L); have hF:=Bank.Τilt (K.wind i hf 1) hX; have hG:=Bank.Τilt (K.wind i hg 1) hY
    have hz := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hm) hx'; intro A; refine ⟨hF.earns.trans hz,hG.earns.trans hz,?_⟩
    have hv := delta K (k:=1) (fun i=>(hp i).slips (by omega)) i ‹0 ≤ p› ha hf hg; have hp₀:= (K.wind i hf 1 |>.Τilt hZ).fest (Bank.Τilt hv hY); let p₀:= L.length
    have hs0 : Bank μ 0 (X₀ f-X₀ g) (v*((L.length:ℝ)*((p*c)*w^(L.length-1)))+(p*z'*v)*w^L.length):=by
        convert! hp₀ using 1; ext x; dsimp only [X₀]; simp only [Pi.add_apply,Pi.sub_apply]; ring
    unfold A; rw [← integral_sub' hF.meets hG.meets]; refine hs0.earns.trans ?_
    calc
       _ ≤ v*((m:ℝ)*((p*c)*w^m))+(p*z'*v)*w^m := by
           have hi':= pow_le_pow_right₀ hK hm; have he:= pow_le_pow_right₀ hK (show L.length-1 ≤ m by omega); have hZ:= hx'; have ht:=(zero_le_one.trans hΩ); have hp:=zero_le_one.trans hK; have hX:0≤p:= ‹0≤p›; gcongr
       _ ≤ v*((m:ℝ)*((p*c)*w^m))*z'+(p*z'*v)*w^m:= add_le_add_left (le_mul_of_one_le_right (by have hp:=zero_le_one.trans hK; have ht:0≤p:= ‹0≤p›; positivity) hΩ) _
       _ = _:= by unfold z'; ring
end FetchD
end YM.MSbar.Kelvin
