import YM.MSbar.LocalSD.Correct
import YM.MSbar.Fusion.Wings
/-!
Fibre summation commutes with pushing and **after normalization**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bulk
open Lattice Wilson RG Filter Function MeasureTheory PhysicalNext.Repeat.Lotus
open Push Finset Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{R:Rep G f}{I:Type}[Countable I]
    (V:Config G c)
variable {a σ C δ Λ w t d u:ℝ}
   (h:R.Lawful σ C Λ δ w)(K:MergeProof.Menu.Arsenal R)(M : I→ Fibre S R)
include h
set_option quotPrecheck false
local notation "nL"=> R.activities
variable (hz:∀ i,∃ j,(M i).turn=Wing.gasKey j)
omit [Countable I] in
lemma buried (N:Fibre S R) (j:ℕ)(he:N.turn=Wing.gasKey j)
    {b:ℕ→ℝ}(hb : Summable b)(hy : ∀ i,0≤b i∧∀ U,‖R.activities.K i U‖≤b i)(U : Config G f): ‖N.cicada U‖ ≤ Real.exp (R.exponent U)* (N.weight*Real.exp (∑' i,b i)):=by
   let x : Set (Finset ℕ):={k|j∈k}; let g(k : x):=N.bun k.val U; let v k:=∏ i∈k,b i
   have ht : ∀ k:Finset ℕ,k∉x → N.bun k U=0:= fun k h=> by unfold Fibre.bun Fibre.bill; simp only [he,if_neg (show ¬ Wing.Occupied (.gasKey j) k from (show j∉k from h)),ite_self]
   have hh := (N.bud h).absolute U; let f(k:Finset ℕ):=‖N.bun k U‖; have hg:=((hasSum_subtype_iff_of_support_subset (s:=x) (by
       rintro i hi; refine by_contra fun hv=> ?_; exact hi (by change ‖N.bun _ _‖=0; rw [ht i hv,norm_zero]))).2 (hh.hasSum : HasSum f _))
   let p(k:x):=k.val.erase j; have hp : Injective p :=by rintro k l (hc:p k=p l); refine Subtype.ext ?_; rw [← insert_erase k.property,← insert_erase l.property]; congr
   have hs : 0 ≤ N.weight:= N.profit; have hk(i):0≤b i:=(hy i).1
   have h₀ i: 0 ≤ v i:= prod_nonneg fun j _=>hk j; have hq : Summable v:=summable_finsetProd_of_summable_nonneg hk hb
   have heq(y:x): f y.val ≤ N.weight*v (p y):=by
       unfold f Fibre.bun; split
       next h=> unfold Fibre.bill; rw [he,if_pos (show Wing.Occupied (.gasKey j) y.val from y.prop),norm_mul,norm_prod]; exact mul_le_mul (N.earn _) (prod_le_prod (fun i _=>norm_nonneg _) (fun j _=>(hy j).2 _)) (prod_nonneg fun i _=>norm_nonneg _) hs
       rw [norm_zero]; exact mul_nonneg hs (h₀ _)
   have hF:= (show ∑' k:x,f k.val≤∑' k:x,N.weight*v (p k) from hg.summable.tsum_le_tsum heq ((hq.comp_injective hp).mul_left _)); rw [tsum_mul_left] at hF -- syntax
   have hv:= (show ∑' i:x,v (p i)≤ ∑' i,v i from ?_).trans (BetaTransport.exponential_sum hk hb)
   · unfold Fibre.cicada; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
     exact (norm_tsum_le_tsum_norm hh).trans ((hg.tsum_eq.symm.trans_le hF).trans (mul_le_mul_of_nonneg_left hv hs))
   exact Summable.tsum_le_tsum_of_inj p hp (fun i _=>h₀ i) (fun i=> le_rfl) (hq.comp_injective hp) hq
omit [Countable I] in
lemma pointed (hu:SumBudget (fun i=> R.p.mass (M i).crest (M i).weight) u) (hz:∀ i,∃ j,(M i).turn=Wing.gasKey j) : Dominated (fun i=>(M i).cicada):=by
    obtain ⟨b,hb,hH⟩:=RG.Activities.K_total h.labels.boundK
    let t:= Real.exp (∑' i,b i); let F U:= Real.exp (R.exponent U); obtain ⟨q,hq⟩:= ((R.exponentEnv h).exp).cost
    have ht := (BetaTransport.budget_unweighted (fun i=>(M i).profit) hu).2.1
    refine ⟨_,(ht.mul_right t).mul_left q,fun i U=>?_⟩
    obtain ⟨j,hv⟩:= hz i; exact (buried h (M i) _ hv hb hH U).trans (mul_le_mul_of_nonneg_right ((le_abs_self (F U)).trans (hq _)) (mul_nonneg (M i|>.profit) (Real.exp_pos _).le))
variable (hP:Psalm S R t d)(hk:S.IsKernel R.beta G)(hv:flags t V=∅)
include hP hk V hv
lemma remit (Q:Config G f→ℝ)(hQ: ∀ U,HasSum (fun i=> (M i).cicada U) (Q U)) (hu:SumBudget (fun i=> R.p.mass (M i).crest (M i).weight) u)(hz:∀ i,∃ j,(M i).turn=Wing.gasKey j) (ht:0≤d)(hj:0≤ S.push R.beta R.eval V) : ‖S.push R.beta Q V‖ ≤ S.push R.beta R.eval V*(d*u):=by
    obtain ⟨b,hb,hB⟩:=pointed h M hu hz
    let p:= S.push R.beta R.eval V; let c U:= S.density R.beta U V; let f i:= S.push R.beta (M i|>.cicada) V
    have hE i : Integrable (fun U: Config G _=> c U* (M i|>.cicada U)) (prior G _):= StepData.push_slice hk V _ ((M i|>.sells h).1.integrable _)
    let A i U:= c U*(M i|>.cicada U); obtain ⟨W,hW⟩:=hk.bound; have hs i U: ‖A i U‖ ≤ W*b i := (norm_mul _ _|>.le).trans (mul_le_mul ((Real.norm_of_nonneg (hk.positive U V)).trans_le (hW U V)) (hB i U) (norm_nonneg _) ((hk.positive U V).trans (hW U V)))
    have he:HasSum f (S.push R.beta Q V):=by
       have hy i: Integrable (A i) (prior G _):=hE i
       have hb(i): (∫ U,‖A i U‖∂prior G _) ≤ W*b i := le_trans (integral_mono (hE i|>.norm) (integrable_const (W*b i)) (hs i)) (le_of_eq (by simp))
       have hh:= hasSum_integral_of_summable_integral_norm hy ((‹Summable b›.mul_left W).of_nonneg_of_le (fun i=>integral_nonneg fun _=> norm_nonneg _) (g:=fun i=>∫ U,‖A i U‖∂prior G _) hb)
       simp_rw [show ∀ U, (∑' i,A i U)=c U*Q U from (fun U=> ((hQ U).mul_left _).tsum_eq)] at hh; exact hh
    have hp: 0≤ p*d:= mul_nonneg hj ht
    rw [← he.tsum_eq]; refine le_trans (norm_tsum_le_tsum_norm he.summable.norm) ?_
    have hg := budget_scale hp hu
    rw [← mul_assoc]; apply le_trans _ hg.2.2; refine he.summable.norm.tsum_le_tsum (fun i=> ?_) hg.2.1
    obtain ⟨j,hj⟩:= hz i; exact (hP (M i) j hj V hv).trans_eq (mul_assoc ..).symm
end YM.MSbar.Bulk
