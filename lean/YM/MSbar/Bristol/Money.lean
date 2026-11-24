import YM.MSbar.Bristol.CoinP
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Lodge Measuring RawP
variable {G:Gauge}{c:Side}{σ:Type}[Fintype σ][DecidableEq σ]
variable {A w B C b r a d v Y e:ℝ}{T W:List σ}{p i j m k s:ℕ}{g: Positions σ→ℝ}{L:σ→ Site c} (u:σ)
noncomputable def peaks (L:σ→ Site c)(T:List σ):= Whisk.extent (Whisk.zone L ∅ T)
noncomputable def shorn (p:ℕ)(l:σ→Site c)(a K t:ℝ)(G:List σ) := if peaks l G≤p then t else K*RawP.raiseQ l a G
variable (ha: 0 < a)(h:Multiplicity L k)(hv:a*(m+2)+b≤ r)(hb:0 ≤ b)
variable (ht:∀ i:ℕ, (1+(i:ℝ))^p ≤ Y* Real.exp (a*i)) (hx:0≤C)(hh:0≤d)
include h ha hv hb ht hx hh
local notation "M₀"=> ((k:ℝ)*countCost a)
noncomputable def checkU (C Y d b a:ℝ)(k p m j:ℕ):= d*liftW b p j*(CrossH.cities k j:ℝ)^m+C*Y*Real.exp (-a*j)*(k*countCost a)^m
lemma churn (hp':0≤Y) : Yarn m (fun T:List σ=> shorn j L r C d (u::T)*swipe L b p (u::T))≤ checkU C Y d b a k p m j:=by
      let H(x:σ):= Decay a (L u) (L x); have hv'(i):0 ≤ H i:=(Real.exp_pos _).le; let f(x:List σ):=(x.map H).prod; have hf(t):0 ≤ f t:=List.prod_nonneg (List.forall_mem_map.mpr (fun i _=> hv' i))
      have hz(k:ℕ):Yarn k (fun T:List σ=>f T)=(∑ i:σ,H i)^k:=by induction k with|zero=>simp [f,Yarn]|succ q ih=> rw [twilled]; unfold f; simp only [List.map_cons,List.prod_cons]; simp_rw [sheen]; change (∑ i,H i*Yarn q f)=_; rw [← sum_mul, ih,pow_succ'] -- syntax f
      let A:= curbL L (L u) j; let Y':=d*liftW b p j; let z:= C*Y*Real.exp (-a*j)
      apply le_trans (b:=Yarn m (fun t=> Y'*CrossH.pulse A t+z*f t)) ?_ ?_; swap
      · rw [pockets,sheen,sheen, spooler,hz]; have hu : (A.card:ℝ) ≤ ↑(cities k j):= Nat.cast_le.mpr (dressP L h _ _); exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hu m) (mul_nonneg hh (wpos ..|>.le))) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun i _=>hv' i) (Multiplicity.count L h ha (L u)) m) (mul_nonneg (mul_nonneg hx hp') (Real.exp_pos _|>.le)))
      apply shiny; intro i he; let A' := peaks L (u::i); unfold shorn; split
      next hi=>
          have hh'(k)(hk:k∈i):k ∈A:=mem_filter.mpr ⟨mem_univ _, le_trans ?_ hi⟩; rotate_left;
          · have hx(v)(hh:v∈u::i):L v∈ Whisk.zone L ∅ (u::i):=mem_union_right ∅ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨v,hh,rfl⟩)); exact curve (hx k (List.mem_cons_of_mem _ hk)) (hx u (List.mem_cons_self ..))
          rw [CrossH.pulse,if_pos hh',mul_one]; apply (mul_le_mul_of_nonneg_left (w_more hi hb p) hh).trans; exact le_add_of_nonneg_right (mul_nonneg (show 0≤z from by unfold z; positivity) (hf _))
      next hi=>
          apply le_trans _ (le_add_of_nonneg_left ?_); swap;· exact mul_nonneg (mul_nonneg hh (wpos ..|>.le)) (by unfold CrossH.pulse; split <;> norm_num) -- y
          have hg1:Real.exp (-(a*m)*(A':ℝ)) ≤ f i:=by
              have hi(i':σ)(hi:i'∈i): Real.exp (-a*A') ≤ H i':=by
                 apply Real.exp_monotone; have hh(v)(hv:v∈u::i): L v∈Whisk.zone L ∅ (u::i):= mem_union_right ∅ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨v,hv,rfl⟩)); exact mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (curve (hh _ (List.mem_cons_self ..)) (hh i' (List.mem_cons_of_mem u hi)))) (neg_nonpos.mpr ha.le)
              have h(t:List σ)(he:t⊆i):Real.exp (-a*A')^t.length ≤ f t:=by induction t with |nil=>simp [f]|cons j t ih=>rw [List.length_cons,pow_succ']; exact mul_le_mul (hi _ (he (List.mem_cons_self ..))) (ih (fun _ h=> he (List.mem_cons_of_mem _ h))) (by positivity) (hv' _)
              have he':=h i (List.Subset.refl _); rw [he,← Real.exp_nat_mul] at he'; refine le_trans (le_of_eq (congr_arg Real.exp ?_)) he'; ring
          have hY:0 ≤ z:=by unfold z; positivity
          change C*Real.exp (-r*A') * ((1+(A':ℝ))^p*Real.exp (b*A')) ≤ z*f i
          refine le_trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (ht A') (Real.exp_pos _|>.le)) (by positivity))) (le_trans ?_ (mul_le_mul_of_nonneg_left hg1 hY)); unfold z; have hA:j≤ A':= by unfold A'; omega
          rw [mul_assoc C, mul_assoc Y,mul_assoc (C*Y),mul_assoc C]
          rw [mul_left_comm (Real.exp _) Y,← Real.exp_add,← Real.exp_add,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hx; apply mul_le_mul_of_nonneg_left _ hp'; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr hA) ha.le, mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (α:=ℝ) A')]
end YM.MSbar.Bristol
