import YM.MSbar.Whisk.Volvo
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao PowerSeries Omnibus
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ][DecidableEq σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side}{l : σ→ Site n}{W: Finset (Site n)} {Y Z:Finset (Site n)} {x y z:Site n}{ξ : View σ}
variable {m p q d :ℕ} {S r a b t u v B D E :ℝ}{f g F G : PowerSeries (Pot σ)}
variable {k k':σ→σ→ℝ}
local notation "J"=> juncture
local notation "µ"=> PowerSeries.coeff
set_option quotPrecheck false
local notation "K!"=>normalized
variable (H₀:Gain l x a B p k k' b D)
section Spin
variable (i j:ℕ)
def Ride (F:PowerSeries (Pot σ))(k:σ→σ→ℝ)(i j:ℕ):=low (normalized k F) i j
def tolly (F:PowerSeries (Pot σ))(k:σ→σ→ℝ)(i j:ℕ):= (∑ p∈Finset.antidiagonal i, ∑ q∈ Finset.antidiagonal j,(1/2:ℝ) • (juncture k (Ride F k p.1 q.1) (Ride F k p.2 q.2)))
lemma lamp (F:PowerSeries (Pot σ))(h:Kind F) (k:σ→σ→ℝ): Ride F k i (j+1)=(j+1:ℝ)⁻¹ • (stove k (Ride F k i j) + tolly F k i j):=by
   rw [Ride, screw h]; unfold tolly
   apply congr_arg; congr 1
   unfold cuts juncture; simp_rw [Finset.smul_sum]; -- Σσ→ p×r
   simp_rw [smul_smul,show ∀ a b, (1/2:ℝ)*k a b=k a b/2 from fun a b=>by ring]
   let C:=Finset.antidiagonal i; let D:=Finset.antidiagonal j
   rw [← Finset.sum_product',sum_comm]; refine sum_congr rfl (fun p hp=>?_); rw [sum_comm]; apply sum_congr rfl; intro q _; rw [← Finset.sum_product']; rfl 
 -- determine order
end Spin
-- All k counts.Step.Bool.Compact. product.S. No root covariance.New.
variable (hf:Kind f)(hg:Kind g)(hF:Kind F)(hG:Kind G)
noncomputable def stair (m b p N : ℕ)(k t : ℝ) := t+k*t+(((p+1)*(N+1):ℝ) * ((4*2^(m+2*b))*(t^2+k*t^2)))
noncomputable def rail (m b p :ℕ)(k t:ℝ)(N:ℕ) := match N with |0=> t|r+1=> rail m b p k t r + stair m b p r k (rail m b p k t r)
local notation "L"=>Omnibus l x a B p
include hf hg hF hG H₀
lemma dawnP (M:ℕ)(hi:∀ q'≤ d,Omnibus l x a B p (m+2*M) ξ (PowerSeries.coeff q' f) (PowerSeries.coeff q' g) (PowerSeries.coeff q' F) (PowerSeries.coeff q' G) t D)(j) : j≤ M → ∀ q≤d,∀ r≤j, L (m+2*(M-j)) ξ (Ride f k q r) (Ride g k' q r) (Ride F k q r) (Ride G k' q r) (rail m M d b t j) D := by
    induction j with
    | zero=> intro hj q h r hr; have hf' : r=0:= Nat.eq_zero_of_le_zero hr; simp only [Ride,hf',began hf,began hg,began hF,began hG, Nat.sub_zero]; exact hi _ h
    | succ j ih =>
       intro hj q' hv r H; specialize ih (by omega); let m':=(m+2*(M-(j+1))); let t':=rail m M d b t j 
       have hml:m+2*(M-j)=m'+2:=by dsimp only [m']; omega
       have hp'(i j')(h:i≤ d)(he: j'≤ j):L (m'+2) ξ (Ride f k i j') (Ride g k' i j') (Ride F k i j') (Ride G k' i j') t' D:=by rw [← hml]; exact ih i h _ he
       let T:= (4*2^m')*(t'^2+b*t'^2); let K':=stair m M d j b t'
       have he:= hp' q' j hv le_rfl; have hh': 0≤ t':=he.bulk.input.1; have hu:=H₀.full.hope; have hs:0 ≤ T:=by unfold T; positivity
       have hk:0≤ K':=by unfold K' stair; positivity
       by_cases hr: r=j+1
       swap
       · exact (hp' q' r hv (by omega)).tension H₀.soft (by unfold m';omega) (le_add_of_nonneg_right hk)
       subst r
       rw [lamp _ _ _ hf,lamp _ _ _ hg,lamp _ _ _ hF,lamp _ _ _ hG]
       let u:= Finset.antidiagonal q';let v₀:=Finset.antidiagonal j; let X₀:=(u.card:ℝ)*( (v₀.card:ℝ) * T); have hx0:0≤X₀:=by unfold X₀; positivity
       have hw :Omnibus l x a B p m' ξ (tolly f k q' j) (tolly g k' q' j) (tolly F k q' j) (tolly G k' q' j) X₀ D:=by
           unfold X₀; rw [show (u.card:ℝ)*(↑v₀.card*T)=∑ i∈u,∑ j∈v₀,T from ?_]; swap; · rw [sum_const, nsmul_eq_mul,sum_const, nsmul_eq_mul] -- edit
           unfold tolly; apply Omnibus.pooling; rintro ⟨i1,i2⟩ hx; have hh:i1+i2=q':=mem_antidiagonal.mp hx; apply Omnibus.pooling; rintro ⟨j1,j2⟩ hp; have hk : j1+j2=j:= mem_antidiagonal.mp hp; let A:=(hp' i1 j1 (by omega) (by omega)); let B':=hp' i2 j2 (by omega) (by omega); exact ((Omnibus.transit H₀ A B').scaled (1/2:ℝ)).tension H₀.soft le_rfl (by change |(1/2:ℝ)| *T ≤ T; simp; linarith only [hs])
       let t₀:=((j+1:ℝ))⁻¹; let D₀:=t'+b*t'+X₀
       have hg: |t₀| ≤ 1 := by unfold t₀;rw [abs_inv,abs_of_pos (by positivity)]; exact inv_le_one_of_one_le₀ (by norm_cast; omega)
       refine ((Omnibus.addN (Omnibus.rain H₀ he) hw).scaled t₀).tension H₀.soft le_rfl (le_trans (b:=D₀) ?_ ((le_trans (b:=K') ?_ (le_add_of_nonneg_left hh'))))
       · unfold D₀; exact mul_le_of_le_one_left (by positivity) hg
       unfold D₀ X₀ K' stair u v₀; rw [Nat.card_antidiagonal,Nat.card_antidiagonal, ← mul_assoc];
       unfold T; push_cast; gcongr <;> (first|omega|norm_num|unfold m';omega)
end YM.MSbar.Whisk
