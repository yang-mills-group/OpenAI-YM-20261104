import YM.RG.History
import YM.Push.ABSOLUTE_SUMS.Product
/-!
# First degree of a forced-list credit at fixed U
Fixed activities.permutations: ONE for all b. Indicators not varying on b.
No ratio through a forced tag. Absolute ℓ¹ envelopes: gross global constants
are OK for taking the tangent once at each *fixed* finite pair.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Trace13.Response
open Function Set Filter RG Lattice Wilson Finset MeasureTheory Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius NNReal Classical BigOperators
variable {G:Gauge}{n:Side}

lemma total_E {X:Activities G n}{p:BudgetPoint}{d:ℝ}(H:X.EBound p d):
    ∃ c,SumBudget c ((Fintype.card (Site n):ℝ)*d)∧∀ i,p.supBounds (X.reg i).site (X.reg i).support (X.E i) (c i):=by
   obtain ⟨c,hc,hf⟩:= H
   refine ⟨c,?_,hc⟩
   let u(x:Site n)(i:ℕ):= if (X.reg i).site=x then p.mass (X.reg i).support (c i) else 0
   apply budget_mono (f:=fun i=>∑ x:Site n,u x i) _ (fun i=>(hc i).1)
   · intro i; simp only [u, sum_ite_eq,Finset.mem_univ,↓reduceIte]; exact p.loMass _ _ (hc i).1
   simpa only [sum_const,card_univ,nsmul_eq_mul] using! budget_over Finset.univ u (fun _=>d) (fun x _=>hf x)

lemma total_K {X:Activities G n}{p:BudgetPoint}{w:ℝ}(H:X.KBound p w):
    ∃ c,SumBudget c ((Fintype.card (Site n):ℝ)*w)∧∀ i,∀ U,‖X.K i U‖ ≤ c i:=by
   obtain ⟨c,hc,hf⟩:= H
   refine ⟨c,?_,fun i U=>(hc i).2 U⟩
   let q (x:Site n)(i:ℕ):= if x∈(X.forced i).support then p.mass (X.forced i).support (c i) else 0
   apply budget_mono (f:=fun i=>∑ x:Site n,q x i) _ (fun i=>(hc i).1)
   · intro i
     obtain ⟨x,hx⟩:=(X.forced i).inventory_ne.mono (X.forced i).inventory_sup
     exact ((p.loMass _ _ (hc i).1).trans_eq (show q x i=_ from if_pos hx).symm).trans <| Finset.single_le_sum (fun y _=> (hf y).1 i) (Finset.mem_univ x)
   simpa only [sum_const,card_univ,nsmul_eq_mul] using! budget_over Finset.univ q (fun _=>w) (fun x _=>hf x)

section petrol
variable {ι:Type*}

open scoped Classical in
def fee (x y:ι→ℝ) (s:Finset ι) := ∑ i∈s, y i * ∏ j∈s.erase i,x j
lemma fee_add (x y:ι→ℝ){s:Finset ι}{i:ι}(he:i∉s): fee x y (insert i s) = y i*(∏j∈s,x j)+x i *fee x y s:=by
    unfold fee; rw [Finset.sum_insert he, erase_insert he, Finset.mul_sum]; congr 1
    refine Finset.sum_congr rfl fun j hj=> ?_; have hu:= ne_of_mem_of_not_mem hj he
    rw [Finset.erase_insert_of_ne hu.symm, Finset.prod_insert (Finset.notMem_mono (erase_subset ..) he)]; ring

variable {x y:ι→ℝ}{z:ℝ}
open scoped Classical in
def wager (x y:ι→ℝ) (z:ℝ) (s:Finset ι):= (∏i∈s,(x i+z*y i))-(∏i∈s,x i)-z*fee x y s
lemma rough {f:ι→ℝ} (he:∀ i,‖x i‖ ≤ f i)(hs:∀ i,‖y i‖ ≤ f i)(s:Finset ι): ‖fee x y s‖ ≤ ∏i∈s,2*f i:=by
   have h i:0≤f i:= (norm_nonneg _).trans (he i)
   induction s using Finset.induction_on with
   | empty=> simp [fee]
   | @insert i t hit ih=>
     rw [fee_add x y hit, prod_insert hit]; refine (norm_add_le ..).trans ?_
     simp only [norm_mul, norm_prod]
     have hg := mul_le_mul (hs i) (Finset.prod_le_prod (s:=t) (g:=fun i=> 2*f i) (fun i _=>norm_nonneg (x i)) (fun i _ => le_trans (he i) (by linarith [h i]))) (Finset.prod_nonneg (fun i _=>norm_nonneg (x i))) (h i)
     apply le_trans (add_le_add hg (mul_le_mul (he i) ih (norm_nonneg _) (h i))); linarith

lemma regular {f:ι→ℝ} (he:∀ i,‖x i‖ ≤ f i)(hs:∀ i,‖y i‖ ≤ f i)(hz : ‖z‖≤1) (s:Finset ι):
    ‖wager x y z s‖ ≤ z^2 * ∏ i∈s,4*f i:=by
    have h i:0≤f i:= (norm_nonneg _).trans (he i)
    induction s using Finset.induction_on with
    | empty=> simp [wager,fee]; positivity
    | @insert i t hit ih=>
       have hx : wager x y z (insert i t)= (x i+z*y i)*wager x y z t+ z^2*(y i*fee x y t):= by
          unfold wager; rw [prod_insert hit,prod_insert hit,fee_add x y hit]; ring
       have hy: ‖fee x y t‖ ≤ ∏i∈t,4*f i:= (rough he hs t).trans (Finset.prod_le_prod (fun i _=>by have := h i; positivity) (fun i _=>by linarith [h i]))
       have hu: ‖x i+z*y i‖ ≤ 3*f i:= (norm_add_le ..).trans (by rw [norm_mul]; nlinarith only [mul_le_mul hz (hs i) (norm_nonneg _) zero_le_one, h i, he i])
       rw [hx,prod_insert hit]; refine (norm_add_le ..).trans ?_; simp only [norm_mul,Real.norm_of_nonneg (sq_nonneg z)]
       refine le_trans (add_le_add (mul_le_mul hu ih (norm_nonneg _) (by have :=h i; positivity)) (mul_le_mul_of_nonneg_left (mul_le_mul (hs i) hy (norm_nonneg _) (h i)) (sq_nonneg _))) ?_; ring_nf; rfl
end petrol

section vital
-- require same labels/addressing; `P` serves as rates, shares numbering too
variable (X Y P:Activities G n) (p:BudgetPoint) (z:ℝ)
local notation "cost" => (Fintype.card (Site n) :ℝ)
open scoped Classical in
def diesel (i : Finset ℕ)(U:Config G n): ℝ:= if X.admissible p U i then fee (X.K · U) (P.K · U) i else 0

def rails (U : Config G n):= ∑' i:Finset ℕ,diesel X P p i U

variable {X Y P p z} {d D w W:ℝ}
variable (hx : X.Valid p d w) (hv:P.Valid p D W)

include hx hv
lemma subsidy (U : Config G n): SumBudget (fun i=> ‖diesel X P p i U‖) (Real.exp (2*(cost*w+cost*W))):=by
    obtain ⟨x,h₁,hX⟩:= total_K hx.boundK; obtain ⟨y,h₂,hY⟩:= total_K hv.boundK
    let f i:= x i+y i
    refine budget_mono (Product.set_products (budget_scale zero_le_two (budget_plus h₁ h₂))) (fun i=>norm_nonneg _) fun i=> ?_
    rw [diesel]; split
    next=> exact rough (f:=f) (fun i=> (hX i U).trans (le_add_of_nonneg_right (h₂.1 i))) (fun i=>(hY i U).trans (le_add_of_nonneg_left (h₁.1 i))) _
    simp only [norm_zero]; apply Finset.prod_nonneg; intro i _; exact mul_nonneg zero_le_two (add_nonneg (h₁.1 i) (h₂.1 i))

lemma rebate (U:Config G n) (hm:Y.forced=X.forced) (hk: Y.K=X.K+z • P.K)(hz :‖z‖≤1)(hu: Summable fun i=> Y.gasOccurrence p i U) :
    ‖Y.gas p U-X.gas p U-z*rails X P p U‖ ≤ z^2 * Real.exp (4*(cost*w+cost*W)):=by
    let k i:= diesel X P p i U; let t i:= Y.gasOccurrence p i U - X.gasOccurrence p i U-z*k i
    have ht (i):= fun (he:X.admissible p U i)=> show t i= wager (X.K · U) (P.K · U) z i from by unfold t k diesel Activities.gasOccurrence Activities.admissible at *; rw [hm]; simp only [if_pos he,wager,hk,Pi.add_apply,Pi.smul_apply,smul_eq_mul] -- hk changes? X? only Y
    have hV (i) (hy:¬ X.admissible p U i) : t i=0:=by unfold t k diesel Activities.gasOccurrence Activities.admissible at *; rw [hm]; simp only [if_neg hy, sub_self,mul_zero]
    have h : Y.gas p U-X.gas p U-z*rails X P p U=∑' i,t i:=by
       unfold Activities.gas t k rails; rw [(hu.sub ((Activities.gasSeries hx).summable U)).tsum_sub (((subsidy hx hv U).2.1.of_norm (f:=k)).mul_left z),hu.tsum_sub ((Activities.gasSeries hx).summable U),tsum_mul_left]
    rw [h]; obtain ⟨x,h₁,hX⟩:= total_K hx.boundK; obtain ⟨y,h₂,hY⟩:= total_K hv.boundK
    let f i:=x i+y i
    have hH : SumBudget (fun i=> ‖t i‖) (z^2*Real.exp (4*(cost*w+cost*W))) := by
       refine budget_mono (budget_scale (sq_nonneg z) (Product.set_products (budget_scale (by norm_num:0≤(4:ℝ)) (budget_plus h₁ h₂)))) (fun _=> norm_nonneg _) (fun i=> ?_)
       by_cases hp: X.admissible p U i
       · rw [ht _ hp]; exact regular (f:=f) (fun i=> (hX i U).trans (le_add_of_nonneg_right (h₂.1 i))) (fun i=>(hY i U).trans (le_add_of_nonneg_left (h₁.1 i))) hz _
       rw [hV _ hp,norm_zero]; refine mul_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun i _=> mul_nonneg (by norm_num) (add_nonneg (h₁.1 i) (h₂.1 i))))
    exact (norm_tsum_le_tsum_norm hH.2.1).trans hH.2.2
end vital
end YM.Trace13.Response
