import YM.MSbar.LocalSD.Escrow
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bulk.Recenter
open Lattice Wilson RG Filter Function MeasureTheory PhysicalNext.Repeat.Lotus
open Push Finset Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{R:Rep G f}
variable {a σ C δ Λ w u v y:ℝ}{X:Support f}{κ:Config G f→ Config G f}{g:Config G f → ℝ}
variable (T:Tracks R X κ g S a) (h:R.Lawful σ C Λ δ w)(K:MergeProof.Menu.Arsenal R)(b:ℕ→ℝ)(hg:∀ i,0≤b i∧∀ U,‖R.activities.K i U‖≤ b i)
local notation "X!"=> pay T h K b hg
-- Saturated union cost. q stays i input, no assumed compatible Output gauges.
lemma spanC (p: Chunk R X): coverNumber R.p.B (extent X p) ≤ coverNumber R.p.B X + ∑ i∈p.val, coverNumber R.p.B (need R i) := by
   suffices h:∀ q:Finset ℕ,q⊆p.val→coverNumber R.p.B (X∪q.biUnion (need R))≤coverNumber R.p.B X+ ∑ i∈q,coverNumber R.p.B (need R i) from h p.val subset_rfl
   intro q hp; induction q using Finset.induction with
   | empty=> simp
   | @insert i q hh ih=>
      obtain ⟨x,hx,ht⟩:=Finset.not_disjoint_iff.mp (p.prop.2.1 _ (hp (mem_insert_self ..)))
      rw [biUnion_insert,sum_insert hh,show X∪_= (X∪q.biUnion (need R))∪need R i by grind]; have he := Corona.meets_sum (Finset.mem_union_left (q.biUnion (need R)) hx) ht R.p.B
      exact (he.trans (Nat.add_le_add_right (ih ((subset_insert ..).trans hp)) _)).trans_eq (by omega)
lemma charging (hC : ∀ x:Site f, SumBudget (fun i=> if x ∈ need R i then R.p.mass (need R i) (b i) else 0) w) : SumBudget (fun l:Chunk R X=> R.p.mass (X! l).crest (X! l).weight) (R.p.mass X (a*2)*Real.exp (X.card*w)):=by
    let F i:= if Disjoint X (need R i) then 0 else R.p.mass (need R i) (b i)
    let f x i:= if x∈need R i then R.p.mass (need R i) (b i) else 0; have hv := budget_over X f (fun _=> w) (fun i _=>hC i)
    have H:SumBudget F (∑ y∈X,(fun _=> w) y):= budget_mono hv (fun i=>by unfold F; split; rfl; exact mul_nonneg (Real.exp_pos _).le (hg i).1) (fun i=>by
       unfold F; split
       next => exact hv.1 i
       next h => obtain ⟨x,hx,hP⟩:= Finset.not_disjoint_iff.mp h; exact le_trans (le_of_eq (show R.p.mass _ _=f x i from (if_pos hP).symm)) (single_le_sum (fun x _=> (hC x).1 i) hx))
    have hx := H.2.1; have hF : (∑' i,F i)≤ X.card * w:=by simpa using H.2.2
    let u p:=∏ i∈p,F i; have hu := summable_finsetProd_of_summable_nonneg H.1 hx
    have hH : SumBudget u (Real.exp (X.card*w)):= ⟨fun p=>prod_nonneg fun i _=> H.1 i,hu,(BetaTransport.exponential_sum H.1 hx).trans (Real.exp_monotone hF)⟩
    have ha:0≤ a*2:=mul_nonneg ((abs_nonneg (g 1)).trans (T.blood 1)) zero_le_two
    apply budget_mono (budget_scale (x:=R.p.mass X (a*2)) (show 0 ≤ _ from mul_nonneg (Real.exp_pos _).le ha) (budget_pull _ Subtype.val_injective hH))
    · intro l; exact mul_nonneg (Real.exp_pos _).le (X! l|>.profit)
    intro l
    have hi : u l.val= (∏ i∈l.val,b i)*Real.exp (R.p.supportExponent * ∑ i∈l.val,(coverNumber R.p.B (need R i):ℝ)):=by
        unfold u; rw [Finset.mul_sum, Real.exp_sum,← prod_mul_distrib]; apply prod_congr rfl; intro i hi; unfold F; rw [if_neg (l.prop.2.1 i hi)]; exact mul_comm ..
    change Real.exp (R.p.supportExponent*↑(coverNumber R.p.B (need R (tag K l)))) *((a*2)*∏ i∈l.val,b i) ≤ R.p.mass X (a*2)*u l.val; rw [hi,(chosen K l).1]
    trans Real.exp (R.p.supportExponent*(coverNumber R.p.B X+(∑ i∈l.val, (coverNumber R.p.B (need R i):ℝ)))) * ((a*2)*∏ i∈l.val,b i)
    · apply mul_le_mul_of_nonneg_right _ (mul_nonneg ha (prod_nonneg fun i _=> (hg i).1)); apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ R.p.exponent_pos.le; exact_mod_cast spanC l
    rw [mul_add,Real.exp_add]; unfold BudgetPoint.mass; apply le_of_eq; ring
include T h K
lemma accurate (hp:Psalm S R v y)(hk:S.IsKernel R.beta G)(V:Config G c) (hV:flags v V=∅)(H:0≤S.push R.beta R.eval V)(ht:0≤y) : |S.push R.beta (fun U=>g U*(R.eval (κ U)*Real.exp (R.exponent U-R.exponent (κ U))-R.eval U)) V| ≤ S.push R.beta R.eval V*(y*(R.p.mass X (a*2)*Real.exp (X.card*w))):=by
    obtain ⟨b,hb,hP⟩:= h.labels.boundK; apply remit V h (pay T h K b hb) hp hk hV _ (fun U=>flowers T U h b hb K) (charging T h K b hb hP) (fun i=> ⟨_,rfl⟩) ht H
end YM.MSbar.Bulk.Recenter
