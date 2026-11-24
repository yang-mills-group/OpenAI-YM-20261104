import YM.MSbar.Wave.Touch
import YM.MSbar.Rolling.Light
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open scoped Topology Classical BigOperators ContDiff
variable {σ A: Type} [Fintype σ] {K:ℝ→A→Prop}
open Finset MvPolynomial
local notation "µ"=> PowerSeries.coeff
local notation "V"=> View σ
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
variable (T:PowerSeries (Pot σ)) (b:PowerSeries ℝ)
local notation "i₀"=> homogeneousComponent
lemma hene (x y:ℝ)(v:View σ)(n:ℕ)(F:Pot σ) : MvPolynomial.eval (x •v) (homogeneousComponent n F)= x^n* MvPolynomial.eval v (homogeneousComponent n F):=by
    let S:=i₀ n F; have ht: S.IsHomogeneous n:= homogeneousComponent_isHomogeneous ..; let em := MvPolynomial.eval v; change MvPolynomial.eval _ S=x^n*MvPolynomial.eval v S; rw [← S.support_sum_monomial_coeff]; rw [map_sum,map_sum,mul_sum]; refine Finset.sum_congr rfl (fun i hi=> ?_); simp only [eval_monomial,Finsupp.prod,Pi.smul_apply, smul_eq_mul,mul_pow, Finset.prod_mul_distrib,prod_pow_eq_pow_sum]; have hv:=ht.degree_eq_sum_deg_support hi; rw [←hv]; ring
lemma buys (n:ℕ)(F:Pot σ)(h:F.totalDegree ≤n) : (∑ i∈range (n+1), i₀ i F) = F:=by refine Eq.trans (sum_subset (range_mono (Nat.succ_le_succ h)) (fun i _ hi=> ?_)).symm (sum_homogeneousComponent F); exact homogeneousComponent_eq_zero i F (by simpa only [mem_range, Nat.lt_succ_iff,not_le] using hi)
-- each i fixed. bound deg ≤ i+2.C.Time.Obj
noncomputable def fare (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) (i j:ℕ) := ∑ d∈range (i+2+1), (µ j (b^d * (b⁻¹ ^ i))) • i₀ d (µ i T)
noncomputable def ticket (b:PowerSeries ℝ) (T:PowerSeries (Pot σ)) : PowerSeries (Pot σ) := PowerSeries.mk (fun i=>∑ j∈range (i+1),fare b T j (i-j))
noncomputable def bley (b:PowerSeries ℝ)(T:PowerSeries (Pot σ))(s:Pot σ): PowerSeries (Pot σ) := ticket b T - PowerSeries.mk (fun i=> µ i (b^2-1) • s)
lemma aims {D: Type*} [AddCommMonoid D](n:ℕ)(F:ℕ→ℕ→D) :(∑ i∈ range (n+1),∑ j∈range (i+1), F j (i-j))=∑ i∈range (n+1),∑ j∈range (n-i+1),F i j:=by
    induction n with
    | zero=> simp
    | succ v ih=>
       let a(v i : ℕ):=∑ j∈range (v-i+1), F i j
       let h(i j:ℕ):= ∑ t∈range (i+j),a i t
       rw [sum_range_succ,ih,sum_range_succ (n:=v+1) (f:=fun i=>a (v+1) i)]
       rw [sum_range_succ (n:=v+1) (f:=fun i=>F i (v+1-i)),← add_assoc,← sum_add_distrib]; simp_rw [Nat.sub_self]; apply congr_arg₂
       · refine Finset.sum_congr rfl (fun i hh=>?_); unfold a; have he:i≤v:= Nat.lt_succ_iff.mp (mem_range.mp hh); rw [show v+1-i=v-i+1 by omega,sum_range_succ (n:=v-i+1)]
       exact (by unfold a; simp)
lemma tasteCut (x:V)(n:ℕ)(p:ℝ) : taste n (picture x (ticket b T)) p = ∑ i∈range (n+1), p^i*(∑ d∈range (i+2+1),taste (n-i) (b^d * (b⁻¹ ^i)) p * MvPolynomial.eval x (homogeneousComponent d (µ i T))):=by
    let g(i j):= ∑ d∈range (i+2+1), µ j (b^d*(b⁻¹^i)) * MvPolynomial.eval x (homogeneousComponent d (µ i T))
    let F(i j):=p^(i+j:ℕ)*g i j; have hx(a):p^a*µ a (picture x (ticket b T))=∑ i∈ range (a+1),F i (a-i):=by
        unfold picture ticket; rw [PowerSeries.coeff_map,PowerSeries.coeff_mk,map_sum,mul_sum]; apply Finset.sum_congr rfl; intro i hi; have hi:=mem_range.mp hi; unfold fare F g; rw [show i+(a-i)=a by omega]; simp only [_root_.map_sum,← C_mul',_root_.map_mul,eval_C]
    unfold taste; simp_rw [hx]; rw [aims]; apply Finset.sum_congr rfl; intro i _; unfold F g; simp_rw [pow_add,mul_assoc,← Finset.mul_sum]; congr 1; simp_rw [mul_sum]; rw [sum_comm]; refine Finset.sum_congr rfl (fun j _=>?_); rw [Finset.sum_mul]; exact sum_congr rfl fun a _=>by ring
variable {b} (p:ℕ)(hf:µ 0 b=1)(h:Expanse T 1 p)(x:ℝ→A→View σ)(hx:Price K 0 x)
include h
lemma parcel (b:PowerSeries ℝ) : Expanse (ticket b T) 1 p:=by
    refine ⟨fun i hi=>?_⟩; unfold ticket fare; rw [PowerSeries.coeff_mk]; exact totalDegree_finsetSum_le fun j hj=> totalDegree_finsetSum_le (fun d hd=>(totalDegree_smul_le ..).trans ((homogeneousComponent_isHomogeneous ..).totalDegree_le.trans (by have hu:=mem_range.mp hj; have hh:=mem_range.mp hd; omega)))
variable {F:ℝ→ℝ}(hF:Approx F b p)
include hf hF hx
lemma decks : Price K (p+1) (fun t i=> taste p (picture (F t • x t i) T) (t/F t) - taste p (picture (x t i) (ticket b T)) t):=by
    let W(j d):=homogeneousComponent d (µ j T)
    let g(j:ℕ)(d:ℕ)(t):= F t ^ d* (F t)⁻¹ ^ j
    let χ(j:ℕ)(d:ℕ)(t):= taste (p-j) (b^d * (b⁻¹ ^ j)) t
    let δ(j d:ℕ)(t):= g j d t-χ j d t
    let B(j d:ℕ)(t)(i:A):= t^j*δ j d t*MvPolynomial.eval (x t i) (W j d)
    let R(j:ℕ):=range (j+2+1); refine (Price.bag (X:=K) (range (p+1)) (fun j t i=> ∑ d ∈R j, B j d t i) (fun j hj=> Price.bag _ (fun d=>B j d) (fun d hd=> ?_))).egress (Eventually.of_forall fun t i hi=> ?_)
    · have h':j≤p:=Nat.lt_succ_iff.mp (mem_range.mp hj); have hB: Price K (p-j+1) (fun t i=>δ j d t):= (Price.inherits ((Approx.mul (Approx.powA hF d) (Approx.powA (Approx.invA hF hf) j)).budget (Nat.sub_le p j)) (z:=fun t i=>()) (Eventually.of_forall fun _ _ _=>trivial))
      have he:p+1=j+(p-j+1):=by omega
      rw [he]; exact Price.product (q:=0) ((xrise K j).product hB) (volley x hx _)
    rw [tasteCut]; unfold taste; rw [← Finset.sum_sub_distrib]; refine sum_congr rfl (fun j hj=>?_); rw [picture,PowerSeries.coeff_map]; have hv:j≤p:=Nat.lt_succ_iff.mp (mem_range.mp hj); let f:=µ j T; have he : ∑ d ∈R j,W j d=µ j T:= buys (j+2) (µ j T) (show _≤_ by simpa only [one_mul] using h.profile j hv); nth_rw 1 [← he]; rw [map_sum]; rw [mul_sum,mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro d _; unfold B δ g χ; have hx:MvPolynomial.eval (F t • x t i) (W j d)=_:= hene (F t) (F t) _ _ _; rw [hx]
    unfold taste W; push_cast; rw [div_eq_mul_inv]; ring
end YM.MSbar.Wave
