import YM.RGComparison.Core16.Silk.Wages
/-!
# Quantitative finite-order PowerSeries ledger for using the real seam prices in the readout

No ψ O(log) re-expression implicitly treated as bounded when propagating to Γ/Λ adapters. This sub-calculus uses receipts *prior* to running coupling/fitted positions. Keep any F expansions with variable g' in terms after map, not defining bootstrap price off controls. Quantitative estimates EVERY fixed n, uniform before effective T etc. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Stage
open Silk
open scoped Topology ContDiff BigOperators Classical InnerProductSpace PowerSeries

variable {T B:Lumen.Stage} {P Q:Roll}{c d x:ℝ} {r:ℕ}{u v:ℝ→ℝ}

abbrev pursed (T:Lumen.Stage)(P:Roll)(u:ℝ→ℝ)(r:ℕ)(c:ℝ):= Fk.Allots T (term P) r c u
abbrev factor (x:ℝ)(r:ℕ)(P:Roll):= peval (term P) r x

section ops
variable (H: pursed T P u r c)

namespace pursed
variable {e:ℝ→ℝ}
include H
lemma widen (hv:B.Above T) (he:u=v):pursed B P v r c:= by subst v; exact ⟨H.pos,H.front,fun x hx=> H.earns x (hv.gate.trans hx)⟩
lemma renew (hv:(∀ x,T.L≤x→u (dollar x)=v (dollar x))):pursed T P v r c:= ⟨H.pos,H.front,fun x hx=>(hv x hx) ▸ H.earns x hx⟩
lemma monotone (hv:c≤d) :pursed T P u r d:= ⟨H.pos.trans hv,fun i hi=>(H.front i hi).trans hv,fun x hx=>(H.earns x hx).trans (mul_le_mul_of_nonneg_left hv (pow_pos (dollar_pos _) _|>.le))⟩
lemma expense {g:ℝ}(hg:0<g)(he:g≤dollar T.L): |u g-factor g r P|≤ g^(r+1)*c:=by
   let x:= -Real.log g; have h: dollar x=g:=by unfold dollar x; rw [neg_neg,Real.exp_log hg]
   have hq: T.L≤x:= by have hx:= (Real.log_le_log hg he); unfold dollar at hx; rw [Real.log_exp] at hx; unfold x; linarith only [hx]
   rw [← h]; exact H.earns _ hq
omit H in
lemma factor_sub (P Q:Roll) (x:ℝ)(r:ℕ): factor x r (P-Q)=factor x r P-factor x r Q:= by simp [factor,peval,Zone.eval,term,mul_sub,sum_sub_distrib]
lemma difference (h:pursed T Q v r d):pursed T (P-Q) (u-v) r (c+d):= by
   refine ⟨add_nonneg H.pos h.pos,fun i hi=> ?_,fun x hx=>?_⟩
   · unfold term; rw [map_sub]; exact (abs_sub ..).trans (add_le_add (H.front i hi) (h.front i hi))
   let g:= dollar x; change |u g-v g-factor g r _| ≤ g^(r+1)*(c+d); rw [factor_sub,sub_sub_sub_comm,mul_add]; exact (abs_sub ..).trans (add_le_add (H.earns x hx) (h.earns x hx))
lemma tax_poly (x:ℝ)(h:0≤x)(he:x≤1):|Lam.factor x r P| ≤ (r+1:ℝ)*c:=by
   have hx (i:ℕ): x^i ≤ 1:=pow_le_one₀ h he; refine (abs_sum_le_sum_abs (fun i=> x^i * nth i P) _).trans ((sum_le_sum (g:=fun _=> c) (fun i hi=> (abs_mul ..).le.trans ?_)).trans_eq (by simp)); rw [abs_of_nonneg (pow_nonneg h _)]; exact (mul_le_of_le_one_left (abs_nonneg _) (hx i)).trans (H.front i (Nat.le_of_lt_succ (mem_range.mp hi)))

variable (he:T.L≤x) (h:pursed T Q v r d)
include h he in
lemma stack_keep : |u (dollar x)*v (dollar x) - factor (dollar x) r P *factor (dollar x) r Q| ≤ dollar x^(r+1)*(c*d*(2*(r+1:ℝ)+1)):=by
    let g:= dollar x; let s:ℝ:= r+1; let p:= factor g r P; let q:= factor g r Q; have hM:0≤ c:= H.pos; have hD:0 ≤ d:=h.pos
    have hg:0≤g:= (dollar_pos _).le; have hG:g≤1:=dollar_bound (Lumen.Stage.now he|>.le)
    have hp:|p|≤ s*c:= tax_poly H _ hg hG -- syntax
    have hq:|q|≤ s*d:= tax_poly h _ hg hG
    have hy: |u g| ≤ s*c+c:= (calc _ = |u g-p+p|:= congr_arg abs (sub_add_cancel (u g) p).symm
                       _ ≤ c+s*c:= (abs_add_le ..).trans (add_le_add ((H.earns x he).trans (mul_le_of_le_one_left hM (pow_le_one₀ hg hG))) hp)
                       _ = _:= add_comm ..)
    rw [show u (dollar x)*v (dollar x)-factor (dollar x) r P*_ = u g*(v g-q)+q*(u g-p) from (by change u g *v g - p*q=_; ring)]
    exact (abs_add_le ..).trans ((add_le_add ((abs_mul ..).trans_le (mul_le_mul hy (h.earns x he) (abs_nonneg _) (add_nonneg (by unfold s; positivity) hM))) ((abs_mul ..).trans_le (mul_le_mul hq (H.earns x he) (abs_nonneg _) (by unfold s; positivity)))).trans_eq (by unfold s; ring))
-- Milestone: need truncated polynomial product tail payment explicitly. Use output triangle.
include h
private def leftWall (x:ℝ)(P Q:Roll) (y:ℕ×ℕ) := x^(y.1+y.2)*(nth y.1 P*nth y.2 Q)
def farePoly (r:ℕ):ℝ:=(r+1:ℝ)*((2*r+1:ℕ)+1 : ℕ) -- replace
lemma factor_balance (U:ℝ) (he:0 ≤ U)(hu:U ≤ 1):|factor U r P *factor U r Q-factor U r (P*Q)| ≤ U^(r+1)*((r+1:ℝ)^2 * c*d):=by
    let D := range (r+1); let s := D ×ˢ D; let A:=D.biUnion antidiagonal; let L:= leftWall U P Q
    have hg (y:ℕ×ℕ): y∈ A ↔ y.1+y.2 ≤ r:=by simp [A,D] -- adjust
    have ha : A⊆s :=fun y hy=>by have h:= (hg y).1 hy; exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
    have e : factor U r (P*Q)=∑ i∈A,L i:=by
        unfold A factor peval Zone.eval; rw [Finset.sum_biUnion]; swap; exact fun i a j b h=>Finset.disjoint_left.mpr (fun z hi hj=> h ((mem_antidiagonal.mp hi).symm.trans (mem_antidiagonal.mp hj)))
        apply sum_congr rfl; intro i _; dsimp only; rw [term,PowerSeries.coeff_mul,smul_eq_mul,Finset.mul_sum]; refine sum_congr rfl fun j hj=>?_; unfold L leftWall; rw [mem_antidiagonal.mp hj]
    rw [e,show factor U r P*factor U r Q=∑ i∈s,L i from ?_]; swap
    · unfold factor peval Zone.eval; unfold s; rw [sum_mul,sum_product]; apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _; unfold L leftWall; dsimp only [term,smul_eq_mul,nth]; rw [pow_add]; ring
    rw [← (sum_sdiff ha), add_sub_cancel_right]
    have ht (i) (hi:i∈s\A) : |L i|≤ U^(r+1)*(c*d):=by
       obtain ⟨hp1,hp2⟩:=mem_product.mp (mem_sdiff.mp hi).1; have hz:= mt ((hg i).2) (mem_sdiff.mp hi|>.2); unfold L leftWall; rw [abs_mul, abs_of_nonneg (pow_nonneg he _),abs_mul]; exact mul_le_mul (pow_le_pow_of_le_one he hu (by omega)) (mul_le_mul (H.front _ (Nat.le_of_lt_succ (mem_range.mp hp1))) (h.front _ (Nat.le_of_lt_succ (mem_range.mp hp2))) (abs_nonneg _) H.pos) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (pow_nonneg he _)
    refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=> U^(r+1)*(c*d)) (fun i h=>ht i h)).trans ?_); rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (show ((s\A).card:ℝ) ≤ (r+1:ℝ)^2 from ?_) (show _ from mul_nonneg (pow_nonneg he _) (mul_nonneg H.pos h.pos))).trans_eq (by ring); simp_rw [show (r+1:ℝ)^2=(s.card:ℝ) from (by unfold s D; simp [sq])]; exact_mod_cast card_le_card (sdiff_subset)

private lemma product_coeff (i:ℕ)(hi:i ≤ r): |nth i (P*Q)| ≤ (r+1:ℝ)*(c*d):=by
    apply (robot i (fun i h=>H.front _ (h.trans hi)) (fun i h₀=>h.front _ (h₀.trans hi))).trans; rw [Nat.card_antidiagonal]; apply mul_le_mul_of_nonneg_right ?_ (mul_nonneg H.pos h.pos); push_cast; gcongr

def forecastCost (t:ℕ)(c d:ℝ):= (t+1:ℝ)*(c*d)+ c*d*(2*(t+1:ℝ)+1)+(t+1:ℝ)^2*c*d
lemma product : pursed T (P*Q) (u*v) r (forecastCost r c d):=by
     have hc:=H.pos; have hd:=h.pos; let m:ℝ:=r+1
     refine ⟨(by unfold forecastCost; positivity),fun i hi=>(product_coeff H h i hi).trans ?_,fun x he=>?_⟩
     · unfold forecastCost; exact le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right (by positivity))
     let g:= dollar x; unfold forecastCost; change |u g* v g-factor g r (P*Q)|≤g^(r+1)*(m* _+c*d*(2*m+1)+ m^2*c*d)
     have hp:0≤ g:= (dollar_pos _).le
     refine (abs_sub_le (u g*v g) (factor g r P*factor g r Q) _).trans ((add_le_add (stack_keep H he h) (factor_balance H h g hp (dollar_bound (Lumen.Stage.now he).le))).trans ?_)
     unfold m; rw [mul_add (g^(r+1)), mul_add (g^(r+1))]; gcongr; apply le_add_of_nonneg_left; positivity

-- Negative shift from template valences; keep quantitative bill ζ at RUNNER gate
omit H h
variable {b:ℕ} (J:pursed T P u (r+b) c) -- reorder

def solder (b:ℕ)(P:Roll):Roll:=PowerSeries.mk fun j=> nth (b+j) P
include J
lemma roll_up (h:∀ i:ℕ,i<b→nth i P=0): pursed T (solder b P) (fun x=>u x/x^b) r c:=by
     have he(x:ℝ) : factor x (r+b) P = x^b*factor x r (solder b P):=by
          unfold factor peval Zone.eval; rw [Nat.add_comm r b,Nat.add_assoc,sum_range_add,sum_eq_zero (s:=range b),zero_add]; swap; intro i hi; dsimp only; rw [show term P ..= _ from h _ (mem_range.mp hi)]; exact smul_zero _
          simp only [solder,term,PowerSeries.coeff_mk,pow_add,smul_eq_mul]; rw [mul_sum]; exact sum_congr rfl fun i _=>mul_assoc ..
     refine ⟨J.pos,fun i hi=>?_ ,fun x hx=>?_⟩
     · rw [solder,term,PowerSeries.coeff_mk]; exact J.front _ (by omega)
     let g:= dollar x; have hp:0<g:= dollar_pos _; change |u g/g^b-factor g r _|≤ _; rw [show u g/ _-_= (u g-factor g (r+b) P)/g^b from ?_,abs_div,abs_of_pos (pow_pos hp _),div_le_iff₀ (pow_pos hp _)]
     · exact (J.earns x hx).trans_eq (by rw [show (r+b+1)=r+1+b from by omega,pow_add]; unfold g; ring)
     rw [he g]; field_simp
end pursed
end ops
end YM.RGComparison.Core16.Lam
