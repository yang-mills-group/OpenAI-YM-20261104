import YM.RG12.Strike.Frost
/-! # Critical response isolates ONLY one coupon per singular mark

Offset scale normalization on pointwise measurements. No clearance assumption beyond literal
absence of coincidence. No profile or configuration-direction derivatives held here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable (χ f g:R→ℂ)(x:R)(a b n m:ℕ)(t:ℝ)
-- annulus terms with uncontracted background in predifferentiated chart
abbrev layer (f g:R→ℂ)(x:R)(n:ℕ)(y:R):ℂ:= f y*fresco n g x y
-- relation under dilation: compare EXACT scaling on fields but cutoff at both ends also. --
lemma fresco_law : VectorLaw (fresco n f x) (-(n:ℤ)) := by
  intro y hy r hr
  unfold fresco;rw [rays y hy r hr]; ring
variable {χ f g x a b}
variable (hχ:Base χ)(hf:Garden f a)(hg:Garden g b)
include hχ hf hg
local notation "Eva(" s ")"=> frosted χ f g a b s
-- sign: since E(tx)=scaled E(x) with cutoff χ_t subtract MORE when t smaller,
-- after engineering `Eva(x)-t^dEva(tx)` = toll t (χ_t−χ) both poles.
lemma oar (t:ℝ)(hx:x≠0)(ht:0<t)(ha:3 ≤ a)(hb:3 ≤ b) :
  Eva(x)-(t:ℂ)^(a+b-4)*Eva(t•x)= ∑ n∈Finset.range (a-3), toll χ (layer f g (-x) n) t + ∑ n∈Finset.range (b-3), toll χ (layer g f x n) t :=by
   have ht':(t:ℂ)≠0:=by exact_mod_cast ht.ne'
   let F:=fun y:R=> flakes χ f g a b y; let A(z:R)(n:ℕ):=paid χ (layer f g (-x) n) t z; let B(z:R)(n:ℕ):=paid χ (layer g f x n) t (z-x)
   have he : ∀ᵐ z:R,z≠0∧ z-x ≠0 := ((volume.ae_ne 0).and (volume.ae_ne x)).mono (fun z h=>⟨h.1,sub_ne_zero.mpr h.2⟩)
   have hw : (fun z:R=>F x z - (t:ℂ)^(a+b)*F (t • x) (t • z)) =ᵐ[volume] (fun z=> (∑ n∈range (a-3),A z n)+(∑ n∈range (b-3),B z n)) := he.mono (fun z hz=>by
     unfold F flakes reach; dsimp only; rw [← smul_sub, hf.radial hz.1 ht,hg.radial hz.2 ht,hf.fiber _ hx ht] -- notation? define use argument inference
     rw [← smul_neg, hg.fiber _ (neg_ne_zero.mpr hx) ht]
     simp only [A,B,paid,hunt,bare,logCost,Pi.sub_apply,layer, ← Finset.mul_sum,rainJet]
     rw [pow_add, inv_pow, inv_pow];field_simp; ring)
   have hP(F G:R→ℂ)(p:ℕ)(y:R)(h:Garden F p)(i:ℕ):Integrable (paid χ (layer F G y i) t):= achieved hχ _ (fun x hx=> (h.openSite x hx).continuousAt.mul (fresco_cont ..).continuousAt) _ ht
   have hA(i:ℕ):Integrable (fun z:R=>A z i):=hP f g a (-x) hf i
   have hB(i:ℕ):Integrable (fun z:R=>B z i):=(hP g f b x hg i).comp_sub_right x
   have he:= integral_congr_ae hw
   rw [integral_sub (lively x hχ hf hg hx ha hb) (((lively (t•x) hχ hf hg (smul_ne_zero ht.ne' hx) ha hb).comp_smul ht.ne').const_mul _),integral_const_mul,Measure.integral_comp_smul_of_nonneg (volume) _ _ (hR:=ht.le)] at he
   rw [integral_add (integrable_finsetSum _ (fun i _=>hA i)) (integrable_finsetSum _ (fun i _=>hB i)),integral_finsetSum _ (fun i _=>hA i),integral_finsetSum _ (fun i _=>hB i)] at he
   have hv(i:ℕ): (∫ z:R,B z i)=toll χ (layer g f x i) t := integral_sub_right_eq_self (paid χ (layer g f x i) t) x
   simp_rw [hv] at he
   have hh:(t:ℂ)^(a+b)*(Complex.ofReal (t⁻¹^Module.finrank ℝ R))=(t:ℂ)^(a+b-4):=by
     simp only [show Module.finrank ℝ R=4 by simp,Complex.ofReal_pow, Complex.ofReal_inv,inv_pow]; rw [show (t:ℂ)^(a+b)=(t:ℂ)^(a+b-4)*(t:ℂ)^4 by rw [← pow_add,Nat.sub_add_cancel (by omega:4≤a+b)]]; field_simp
   rw [Complex.real_smul,← mul_assoc] at he; -- t^(-4) maybe zpow
   rw [← inv_pow,hh] at he; exact he
     
-- literal layers above log crit? actual omitted all >. nonresonant toll buys power
omit hg in
lemma money (h:a=4+n+m)(x:R)(hp:0<m):∃ C:ℂ,∀ t:ℝ,0<t→toll χ (layer f g x n) t=C*((t:ℂ)^m-1):=by
   refine coupon hχ _ (fun x hx=> (hf.openSite x hx).continuousAt.mul (fresco_cont ..).continuousAt) ?_ hp
   convert hf.line.mul (fresco_law g x n) using 1
   omega
end YM.RG12.Strike
