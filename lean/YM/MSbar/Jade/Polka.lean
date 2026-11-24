import YM.MSbar.Tilt.WireZ
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Jade
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bout Tilt
variable {σ ι: Type}[Fintype σ][DecidableEq σ]{d k p r:ℕ}{A B K:ℝ}{f g:View σ→ℝ}{x y:View σ}
section
variable [Fintype ι][DecidableEq ι]
local notation "T"=>View σ
open Metric
variable (L:ι→Finset σ)(P:Finset σ)
variable {U:ι→View σ→ℝ} (h:∀ i, U i∘haul σ (L i)= U i)
noncomputable def farQ (P:Finset σ)(W:ι→ Finset σ) := Finset.univ.filter (fun i=>¬ Disjoint (W i) P)
lemma tails (p:ℕ) (hW:∀ i∈Finset.univ,ContDiffAt ℝ ω (U i) 0)(hf:f=ᶠ[𝓝 0] fun x=> ∑ i:ι,U i x): Work.G05.blockTaylor p f= fun x=>∑ i:ι,blockTaylor p (U i) x:=by
    funext u; have hx : (∑ i:ι,U i)=fun x=> ∑ i:ι,U i x:=funext fun x=>Finset.sum_apply ..; unfold blockTaylor; simp_rw [Finset.sum_apply]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; unfold Tensor.diagonal Tensor.coeff; rw [(hf.iteratedFDeriv ℝ i).eq_of_nhds, ← hx, iteratedFDeriv_sum_apply (fun i hi=> (hW i hi).of_le le_top),Finset.smul_sum,_root_.sum_apply] -- inspect
include h
lemma Oscar (i:ι)(hh:i∉farQ P L)(p:ℕ)(hx:∀ i∈Finset.univ\P,x i=y i)(hp:ContDiffAt ℝ p (U i) 0): U i x=U i y ∧ blockTaylor p (U i) x=blockTaylor p (U i) y:=by
    have hd: Disjoint (L i) P:=by by_contra hv; apply hh; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
    let F:= haul σ (L i); have he(z:ℝ): F (z • x)= F (z • y):=by
        funext j; unfold F haul; split; next ht=> have hh:= Finset.disjoint_left.mp hd ht; simp only [Pi.smul_apply,hx j (Finset.mem_sdiff.mpr ⟨mem_univ _, fun hi=> hh hi⟩)]
        rfl
    have hb(z:ℝ): U i (z • x)=U i (z • y):=by nth_rw 1 [← h i]; rw [Function.comp_apply,show haul _ _ _= _ from he _]; exact congr_fun (h i) _
    constructor; · simpa using hb 1
    unfold blockTaylor; rw [Finset.sum_apply, Finset.sum_apply]; refine Finset.sum_congr rfl fun j hj=> ?_; have hh:ContDiffAt ℝ j (U i) 0:= hp.of_le (m:=↑j) (by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hj)); unfold Tensor.diagonal Tensor.coeff; rw [_root_.smul_apply,_root_.smul_apply]; apply congr_arg; exact Eq.trans ((Next.Foundations.iteratedDeriv_on_line hh _).symm) ((congr_arg (fun i:ℝ→ℝ=> iteratedDeriv _ i _) (_root_.funext hb)).trans (Next.Foundations.iteratedDeriv_on_line hh y))
lemma rays_p (p:ℕ) (ht:p+1 ≤ d)(hA:∀ i v, ‖v‖ < A → Allows d (U i) v B) (hx:‖x‖ ≤ K) (hy:‖y‖ ≤ K)(hl:K<A) (hg:∀ i∈ Finset.univ\ P,x i = y i) (hf:f=ᶠ[𝓝 0] fun x=> ∑ i:ι,U i x)(h1:f x=∑ i:ι,U i x)(h2:f y=∑ i:ι,U i y) :
       |(f x-f y)-(blockTaylor p f x-blockTaylor p f y)| ≤ (farQ P L).card*(2* B*K^(p+1)):=by
    let m(x:ι):=U x- blockTaylor p (U x) -- invalid let
    have hW : ∀ i∈Finset.univ,ContDiffAt ℝ ω (U i) 0:= fun i _=> (hA i 0 (norm_zero|>.trans_lt (((norm_nonneg _).trans hx).trans_lt hl))).1
    have hv(i :ι)(x:View σ)(hx: ‖x‖ ≤ K) : |m i x|≤ B*K^(p+1):=by
          have hu:= permit (m:=d) ht (hA i) (hx.trans_lt hl) 0 (Nat.zero_le _)
          rw [Nat.sub_zero,norm_iteratedFDeriv_zero] at hu; exact hu.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) ((hA i _ (hx.trans_lt hl)).nonneg))
    rw [tails p hW hf,h1,h2]; let g(i:ι):= m i x-m i y; rw [show (_-_)-(_-_)=∑ i:ι,g i from (by unfold g m; simp only [Pi.sub_apply,Finset.sum_sub_distrib];ring)]; rw [← Finset.sum_subset (Finset.subset_univ (farQ P L)) (fun i hi hp=> ?_)]; · refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=>(abs_sub ..).trans (add_le_add (hv i x hx) (hv i y hy)))).trans_eq ?_); rw [sum_const,nsmul_eq_mul];ring
    unfold g m; rw [Pi.sub_apply,Pi.sub_apply,(Oscar L P h i hp _ hg ((hW i hi).of_le (m:=p) le_top)).1,(Oscar L P h i hp _ hg ((hW i hi).of_le (m:=p) le_top)).2, sub_self]
omit h
lemma allowance {n:Side}(S:ι→Site n)(J:σ→ Site n)(u:ℕ)(hK : Multiplicity S k) : (farQ P (fun i=>curbL J (S i) u)).card ≤ P.card*cities k u:=by
    let V:= fun j=> curbL S (J j) u; have hp : farQ P (fun i=>curbL J (S i) u) ⊆ P.biUnion V:=by
        intro i hi; have hh:=mem_filter.mp hi|>.2; obtain ⟨j,hj,hV⟩:= Finset.not_disjoint_iff.mp hh; have h:separation (J j) (S i)≤ u:= (mem_filter.mp hj).2; rw [separation_comm] at h; exact Finset.mem_biUnion.mpr ⟨j,hV,Finset.mem_filter.mpr ⟨mem_univ _,h⟩⟩
    refine (card_le_card hp).trans ((card_biUnion_le ..).trans ((sum_le_sum (fun i _=> dressP S hK (J i) u)).trans_eq ?_)); rw [Finset.sum_const,smul_eq_mul]
end
end YM.MSbar.Jade
