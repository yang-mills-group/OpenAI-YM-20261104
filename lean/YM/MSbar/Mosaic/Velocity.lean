import YM.MSbar.Bristol.PriceR
import YM.MSbar.Alto.Suez
/-! Uniform asymptotics toolkit. Used along arbitrary cofinal sequences for finite stages.Witness choice over finite tori: we do not take fixed tor here. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter Asymptotics
open scoped Topology BigOperators ContDiff Classical
variable {ι τ :Type*}{f g X:ι→ℝ}{φ: Filter ι} {a b c δ r :ℝ}
def Run (φ:Filter ι)(X g:ι→ℝ)(b:ℝ):Prop:= ∀ r:ℝ,b<r→∀ᶠ i in φ, |g i| ≤ (X i)^r
def Van (φ:Filter ι)(X g:ι→ℝ) := ∀ b:ℝ, Run φ X g b
namespace Run
variable (hX:Tendsto X φ atTop)
include hX
lemma core (b:ℝ) : Run φ X (fun i=> (X i)^b) b:=by
    intro a h; filter_upwards [hX.eventually_ge_atTop 1] with x hx; rw [abs_of_nonneg (by have hx':=zero_le_one.trans hx; positivity)]; exact Real.rpow_le_rpow_of_exponent_le hx h.le
lemma token (b:ℝ):Run φ X (fun _=>b) 0:=by intro a h; exact ((tendsto_rpow_atTop h).comp hX).eventually_ge_atTop |b|
omit hX in
lemma loosen (h:Run φ X g b)(hv:b≤c): Run φ X g c:= fun a he=>h a (hv.trans_lt he)
omit hX in
lemma cash (h:Run φ X g b)(hv:∀ᶠ i in φ, |f i| ≤ |g i|):Run φ X f b:= fun a he=> (hv.and (h a he)).mono fun i hh=> hh.1.trans hh.2
omit hX in
lemma alter (h:Run φ X f b)(he:f=ᶠ[φ]g):Run φ X g b:=h.cash (he.mono (fun i hi=> le_of_eq (congr_arg abs hi.symm)))
omit hX in
lemma subclock (h:Run φ X g b){t:τ→ι}{q:Filter τ}(hp:Tendsto t q φ): Run q (X ∘ t) (g∘ t) b:=fun a he=> hp.eventually (h a he)
lemma mulR(h:Run φ X g b)(hv:Run φ X f c):Run φ X (fun x => g x*f x) (b+c):=by
    intro r hr; let a:=(r-b-c)/2; have ha:0<a:=by unfold a; linarith; -- funds
    filter_upwards [hX.eventually_gt_atTop 0,h (b+a) (by linarith),hv (c+a) (by linarith)] with x hx he hh; rw [abs_mul]; refine (mul_le_mul he hh (abs_nonneg _) (by positivity : 0 ≤ (X x)^(b+a))).trans_eq ?_; rw [← Real.rpow_add hx,show b+a+(c+a)=r from (by unfold a; ring)]
lemma mulK (h:Run φ X g b)(k:ℝ):Run φ X (fun i=>k*g i) b:=by have he:= (token hX k).mulR hX h; rw [zero_add] at he; exact he
lemma mulY (h:Run φ X g b)(k:ℝ):Run φ X (fun i=>g i*k) b:=by simp_rw [mul_comm]; exact mulK hX h k
lemma addR (h:Run φ X g b)(e:Run φ X f b):Run φ X (fun i=>g i+ f i) b:=by
    intro r he; obtain ⟨z,hz,hZ⟩:=exists_between he
    filter_upwards [h z hz,e z hz,(mulK hX (core hX z) 2) r hZ] with i hi hp hh; exact (abs_add_le ..).trans ((add_le_add hi hp).trans ((le_of_eq (two_mul (X i^z)).symm).trans ((le_abs_self _).trans hh)))
lemma kick (h:Run φ X f b)(e:Run φ X g a)(he:a≤b):Run φ X (fun i=>f i+g i) b:=h.addR hX (e.loosen he)
lemma raise (h:Run φ X g b)(p:ℕ):Run φ X (fun i=>g i^p) (b*p):=by induction p with |zero=> simp only [pow_zero,Nat.cast_zero,mul_zero]; exact token hX 1|succ i ih=> have hx:= ih.mulR hX h; simp_rw [pow_succ]; refine hx.loosen ?_; push_cast; apply le_of_eq; ring
lemma bouquet (h:Run φ X g b)(hb:b<0):Tendsto g φ (𝓝 0):=by
    obtain ⟨z,hz,hZ⟩:=exists_between hb; have hh:Tendsto (fun i=> (X i)^z) φ (𝓝 0):=by
        have hp:= (tendsto_rpow_neg_atTop (show 0 < -z from neg_pos.mpr hZ)).comp hX; rw [neg_neg] at hp;exact hp
    exact tendsto_zero_iff_norm_tendsto_zero|>.mpr (squeeze_zero' (Eventually.of_forall fun i=> abs_nonneg (g i)) (h z hz) hh)
lemma dory (h:Run φ X g b)(hv:b<a): Tendsto (fun i=>g i/(X i)^a) φ (𝓝 0):=by
     have hz: b+-a <0:=by linarith only [hv]
     refine (bouquet hX (h.mulR hX (core hX (-a))) hz).congr' ?_; filter_upwards [hX.eventually_gt_atTop 0] with i hi; rw [Real.rpow_neg hi.le]; rfl
lemma logP :Run φ X (fun i=>Real.log (X i)) 0:=by
    intro a ha; have hp : (fun x:ℝ=> Real.log x) =o[atTop] (fun i=> i^a):= isLittleO_log_rpow_atTop ha -- signature
    filter_upwards [hX.eventually (hp.bound one_pos),hX.eventually_gt_atTop 1] with x hx h; rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (show 0 ≤ X x from le_trans zero_le_one h.le) _ )] at hx; exact hx
lemma exp (h : Tendsto f φ (𝓝 c)):Run φ X (fun x=>Real.exp (f x)) 0:= by
    refine (token hX (1+Real.exp c)).cash (((Real.continuous_exp.continuousAt.tendsto.comp h).eventually (ge_mem_nhds (lt_add_of_pos_left _ zero_lt_one))).mono fun x hx=>?_); rw [abs_of_nonneg (Real.exp_pos _).le]; exact hx.trans (le_abs_self _)
lemma count (T:Finset τ)(g:τ→ι→ℝ)(h:∀ i∈T,Run φ X (g i) b): Run φ X (fun i=>∑ j∈T,g j i) b:=by
     induction T using Finset.induction with|empty=> simp only [Finset.notMem_empty,Finset.sum_empty]; intro r hr; filter_upwards [hX.eventually_gt_atTop 0] with x hx; rw [abs_zero]; positivity
                                            |insert i T hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).addR hX (ih (fun i hx=> h _ (Finset.mem_insert_of_mem hx)))
end Run
namespace Van
variable (hX:Tendsto X φ atTop)
include hX
lemma mulL (h:Run φ X f a)(hx:Van φ X g): Van φ X (fun i=> g i*f i):=by intro b; have he:=(hx (b-a)).mulR hX h; rw [sub_add_cancel] at he; exact he
lemma summa (h:Van φ X f)(hx:Van φ X g) : Van φ X (fun i=>g i+f i) := fun b=> (hx b).addR hX (h b)
lemma castE (ha:a<0) : Van φ X (fun i=> Real.exp (a*Real.log (X i)^2)):=by
    have hp:= Real.tendsto_log_atTop.comp hX; intro b c hh; filter_upwards [ (hp.const_mul_atTop_of_neg ha).eventually_le_atBot c,hp.eventually_ge_atTop 0,hX.eventually_gt_atTop 0] with i hi hx he
    rw [abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos he]; apply Real.exp_monotone; simp only [Function.comp_apply] at hi hx; linarith only [mul_le_mul_of_nonneg_right hi hx]
end Van
lemma cofi {α:Type}{S:ℝ → α→Prop}{T:ℝ→α→ Prop} (h:∀ (x:ℕ→ℝ)(a:ℕ→α),Tendsto x atTop atTop → (∀ i,S (x i) (a i))→ ∀ᶠ i in atTop,T (x i) (a i)) : ∀ᶠ x in atTop,∀ a:α,S x a → T x a:=by
    by_contra hp
    rw [eventually_atTop] at hp; push Not at hp; choose x hx y hy hz using fun i:ℕ=> hp (i:ℝ); have ht:Tendsto x atTop atTop:= tendsto_atTop_mono hx tendsto_natCast_atTop_atTop; obtain ⟨i,he⟩:= (h x y ht hy).exists; exact hz i he
end YM.MSbar.Mosaic
