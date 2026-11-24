import YM.MSbar.Bakery.Roast
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery
open Function Filter Finset Cacao MeasureTheory Whisk PowerSeries Omnibus
open scoped Topology BigOperators Classical ContDiff
variable {σ ι :Type}[Fintype σ] [DecidableEq σ]
open Lattice MvPolynomial Analysis Set Metric
local notation "P"=>Pot σ
local notation "V"=>View σ
local notation "µ"=>PowerSeries.coeff
local notation "Ω"=>PowerSeries.X
variable {x y ξ:View σ}{f F G: PowerSeries (Pot σ)}{X:Set (View σ)}{p m k q j d :ℕ}{t a r b D E M :ℝ} {n:Side}{l:σ→ Site n}{Y W:Finset (Site n)}{z:Site n}{K K':σ→σ→ℝ}
lemma plaster {F :Pot σ} (ha:0≤a)(hp:Vault l W a p m ξ F t): |MvPolynomial.eval ξ F|≤t:=by
   have hx:= hp.2 0 (Nat.zero_le _); change spread l W a p [] * _≤ _ at hx; exact le_trans (le_mul_of_one_le_left (abs_nonneg _) (w_start ha p _)) hx
lemma dock {F: Pot σ} (ha:0≤a)(hb:0≤ b) (hp:∀ v∈X,Vault l {z} (a+b) p 1 v F t)(hv:x∈X)(hx:y∈X)(hs:Convex ℝ X) (hz:0≤ r)(hk:∀ i,|x i-y i|≤ r * Eve b z (l i)): |eval x F - eval y F| ≤ r*t :=by
    obtain ⟨u,hu,H⟩:= cutAt (f:=fun x=> eval x F) [] hs hx hv (fun u _=> (vent F|>.contDiffAt.of_le le_top)); have hC := hp u hu
    rw [show eval x F- eval y F = _ from H]; refine (abs_sum_le_sum_abs ..).trans (le_trans (b:=r*lump l {z} (a+b) p 1 u F) ?_ (mul_le_mul_of_nonneg_left (hC.2 _ le_rfl) hz))
    unfold lump; rw [twilled,mul_sum]; apply Finset.sum_le_sum; intro i hi; rw [abs_mul]; apply (mul_le_mul_of_nonneg_right (hk i) (abs_nonneg _)).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hz
    rw [twillz]; change Eve b z (l i)*|glance _ ([i]) _|≤ _; rw [glance_jet]; unfold rate; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); have hy:Eve b z (l i) ≤liftW (a+b) p (separation z (l i)):= by
       apply le_trans (le_mul_of_one_le_left (Real.exp_pos _|>.le) (w_start ha _ _)); exact le_of_eq (trade ..)
    exact hy.trans (radius_go _ (by simp) (mem_singleton_self _) (add_nonneg ha hb) p)
lemma abroad (ξ:View σ) {F G : P} (ha:0≤a)(h₀ : Tokew l a p m ξ F b)(hu:Vault l {z} a p (m+1) ξ G t) : Tokew l a p m ξ (F+G) (b+t):=h₀.kit (Tokew.quiet z ha hu)
lemma Paired.same {H₀:Pot σ}(h:Tokew l (a+b) p m ξ H₀ t)(ht:0≤ D): Paired l z a b p m ξ H₀ H₀ t D t:=by
    refine ⟨h,h,?_⟩; rw [sub_self]; have hx:=mul_nonneg h.1 ht; refine ⟨hx,fun i=>?_⟩; rw [_root_.map_zero]; exact Quote.nill (mul_nonneg (Real.exp_pos _).le hx)
lemma Starry.same {H₀:Pot σ}(h:Vault l {z} (a+b) p m ξ H₀ t)(ht:0≤ D): Starry l z a b p m ξ H₀ H₀ t D t:=by
    refine ⟨h,h,?_⟩; rw [sub_self]; exact Quote.nill (mul_nonneg h.1 ht)
variable (hx : Kind f)(hp : Gain l z a b p K K' M D)(T:Expanse f j d)
local notation "d'"=>Whisk.ribbon j d
local notation "v'"=> (f+PowerSeries.X^m*F)
include hp
private lemma driverP (hv:0<m)(he:k≤d)(ht:∀ i≤d, Vault l {z} (a+b) p (q+1) ξ (µ i F) t) (hf :∀ i≤d,Tokew l (a+b) p q ξ (µ i f) t): Omnibus l z a b p q ξ (µ k v') (µ k v') (µ k f) (µ k f) (t+t) D:=by
    have hg:=hf k he; have ht₀:=hg.1; let H: Pot σ:= µ k (Ω^m*F)
    have hP : µ k v'=µ k f+ H:= map_add ..
    have h : Vault l {z} (a+b) p (q+1) ξ H t := by
       unfold H; rw [PowerSeries.coeff_X_pow_mul']; split; exact ht _ ((Nat.sub_le ..).trans he); exact Quote.nill ht₀
    rw [hP]; have he' :t ≤ t+t:= le_add_of_nonneg_right ht₀; refine ⟨Paired.same (abroad ξ (add_nonneg hp.sober hp.green) hg h) hp.soft,(Paired.widen (Paired.same hg hp.soft) he' hp.soft he' le_rfl),?_⟩
    rw [add_sub_cancel_left]; exact Starry.same (Quote.widen h he' (by omega)) hp.soft
-- compares formal ratio and all location derivatives under any marker.Support.Y.Scheme.
include T hx
lemma credential (hv:0<m) (T':Expanse (f+PowerSeries.X^m * F) j d)
    (ht:∀ i≤d, Vault l {z} (a+b) p (q+2*Whisk.ribbon j d+1) ξ (µ i F) t) (hf:∀ i≤d, Tokew l (a+b) p (q+2*Whisk.ribbon j d) ξ (µ i f) t) (he:m+k≤d):
    Starry l z a b p q ξ (µ k (growP f F K m)) (µ k (growP f F K' m)) (driver j d q M (t+t)) D (driver j d q M (t+t)) := by
      delta growP Scan; rw [PowerSeries.coeff_mk,PowerSeries.coeff_mk,map_sub,map_sub]; exact (voyage hp (ripple hx F _ hv) (ripple hx F _ hv) hx hx T' T' T T (fun i hi=>driverP hp hv hi ht hf) he).drift
lemma transferPin (hv:0<m) (T':Expanse (f+PowerSeries.X^m*F) j d) (ht:∀ x∈ X,∀ i≤d, Vault l {z} (a+b) p (2+2*Whisk.ribbon j d) x (µ i F) t)(hf : ∀ x∈ X,∀ i≤d,Tokew l (a+b) p (1+2*Whisk.ribbon j d) x (µ i f) t)(he:m+k≤d) (hy:x∈X)(hY:y∈X)(hs:Convex ℝ X)(hz:0≤ r)(hB:∀ i,|x i-y i| ≤ r *Eve b z (l i)):
     let u:= driver j d 1 M (t+t)
     |eval x (µ k (growP f F K m))-eval y (µ k (growP f F K' m))|≤ u* (D+r):=by
   let A:= µ k (growP f F K m); let B:= µ k (growP f F K' m); intro u
   have h(n)(i:n∈ X): Starry l z a b p 1 n A B u D u:= credential hx hp T hv T' (by rw [show 1+2*d'+1=2+2*d' by omega]; exact ht _ i) (hf n i) he
   have hx' := plaster hp.sober ((h y hY).change); have hm:= dock hp.sober hp.green (fun x he=> (h x he|>.input)) hy hY hs hz hB; rw [map_sub] at hx'; change |eval x A - eval y B|≤ _; rw [show eval x A- eval y B=(eval x A-eval y A)+(eval y A-eval y B) by abel]; exact (abs_add_le ..).trans ((add_le_add hm hx').trans_eq (by ring))
end YM.MSbar.Bakery
