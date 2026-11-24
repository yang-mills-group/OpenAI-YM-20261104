import YM.MSbar.Alto.Vinay
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
structure Sampled (n:Side)(A:Stage): Prop where
    bound : ∃ v:ℕ,10*(v+4)<n.val∧ Fintype.card PlaqAxes * (A.paths*A.paths*url n v A.width) ≤1
noncomputable def travelA (R:Stage)(n:ℕ):= (16*(n:ℝ)^10+2)* Real.exp (-R.width*(n/100:ℕ))
lemma retreat (R:Stage) : ∀ᶠ n:ℕ in atTop,∀ i:Side,n=i.val → Sampled i R:=by
    let C:=R.width/100; have hc:0<C:= div_pos R.width_pos (by norm_num); let D:=(Fintype.card PlaqAxes:ℝ)*R.paths*R.paths; have hD:0<D:=by unfold D; have hp:=R.paths_pos; have hx:0 < Fintype.card PlaqAxes:= (by decide); positivity
    let f(n:ℕ) := Real.exp (-C *(n:ℝ)); have hp:Tendsto (fun n:ℕ=> (n:ℝ)^10*f n) atTop (𝓝 0):=by
         let X:= Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 10; have hp:= X.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc); have ht:= hp.div_const (C^10); rw [zero_div] at ht; refine ht.congr' (Eventually.of_forall fun i=>?_); unfold f; change (C*i)^10*_*_⁻¹= _ -- division expression syntax
         field_simp
    have ht:Tendsto f atTop (𝓝 0):=Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
    have hi:Tendsto (fun n:ℕ=> (16*(n:ℝ)^10+2)*f n*(Real.exp (R.width))) atTop (𝓝 0):=by
         have h:= ((hp.const_mul 16).add (ht.const_mul 2)).mul_const (Real.exp R.width); simp only [mul_zero,add_zero,zero_mul] at h; refine h.congr fun _=>?_ ; ring
    filter_upwards [eventually_gt_atTop 1000,hi.eventually (ge_mem_nhds (inv_pos.mpr hD))] with n hn he i hx; subst n; let N:=i.val; let p:= i.val/100
    refine ⟨p,by omega,?_⟩; let W:=url i p R.width; change _*(R.paths*R.paths*W) ≤ _
    have hw: W ≤ D⁻¹:=by
        apply le_trans _ he; have hz : (N:ℝ)< 100*((p:ℝ)+1) := by unfold N; exact_mod_cast (show i.val < 100*(p+1) by omega)
        unfold W url Midpoint.size; rw [site_card, Nat.cast_pow]; rw [mul_assoc (16*(_ :ℝ)^10+2)]; apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity); -- comm ring
        · apply le_of_eq; ring
        unfold f; rw [← Real.exp_add]; apply Real.exp_monotone; unfold C; nlinarith only [mul_le_mul_of_nonneg_left hz.le R.width_pos.le]
    exact le_trans (le_of_eq (by unfold D; ring)) ((mul_le_mul_of_nonneg_left hw hD.le).trans_eq (mul_inv_cancel₀ hD.ne'))
-- finite rents * stages. Need after purchase BetaEntry each J on > destin independent.Delays
open Supply Input
variable (K:MapPrices)
structure BeforeL (j:ℕ)(L:Side)(K:MapPrices)(G:Gauge) : Prop where
    paid (p s:ℕ) : 6≤ s → s≤ j → p≤ j → ∀ i≤j,Host G (seats K j i s) L p s (ceilα K j i)
lemma ceremony (G:Gauge)(j:ℕ) : ∀ᶠ m:ℕ in atTop,∀ g: Side,m=g.val→ BeforeL j g K G:=by
    let s:=Finset.range (j+1)
    have hp(p t i:ℕ)(ht:6≤t):∀ᶠ m:ℕ in atTop,∀ g:Side, m=g.val→ Host G (seats K j i t) g p t (ceilα K j i):=(hoster K j i t p G ht).mono (fun m h g hm=>h g hm.symm) -- remove .L
    -- show finite
    let X(p t i m:ℕ):Prop:=6≤t →∀ g:Side,m=g.val→Host G (seats K j i t) g p t (ceilα K j i)
    have hx:∀ᶠ m:ℕ in atTop,∀ p∈s,∀ t∈s,∀ i∈s,X p t i m:= s.eventually_all.mpr fun p _=> s.eventually_all.mpr fun t _=> s.eventually_all.mpr fun i _=> by by_cases he:6≤t; exact (hp p t i he).mono fun m hm _=>hm; exact Eventually.of_forall fun m he'=> (he he').elim
    filter_upwards [hx] with m hh g hg; exact ⟨fun p t ht hv hx i hi=>hh p (mem_range.mpr (by omega)) t (mem_range.mpr (by omega)) i (mem_range.mpr (by omega)) ht g hg⟩
lemma prepaid (G:Gauge): ∃ f₀:ℕ→ℕ,∀ j:ℕ,∀ g:Side,f₀ j ≤ g.val→ BeforeL j g K G:=by
    choose f hf using fun j=> eventually_atTop.mp (ceremony K G j); exact ⟨f, fun i g he=> hf _ g.val he g rfl⟩
end YM.MSbar.Alto
