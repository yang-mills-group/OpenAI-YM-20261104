import YM.Integration.WilsonCoherentMayerPriorPartitions
import YM.Integration.WilsonCoherentMayerPriorSource

/-! The coefficient bill for the actual older partition depends on the finite set of registered marks. Its uniform upper price is fixed before any cutoff, period or observation point. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorCapacity
open Function Finset Marker Multi Comparison.RG02.Cumulants
open WilsonCoherentMayerPriorPartitions
open scoped Classical BigOperators

variable {V:Type}[DecidableEq V](R:Census V)
def degree:=Fintype.card (Multi.Hot R)
def count:ℝ:=∑p:(parts R).Mode,‖mobiusTop p.val.card‖*(p.val.card:ℝ)

theorem finite (x:Poly R){δ a:ℝ}(non:0≤δ)(one:1≤a)
    (limit:∀i:R.Mode,‖x.part i‖+δ≤a)(s:R.Mode):
    cost x δ s≤count R*a^degree R:=by
  let T:=a^degree R
  have xp(i:Multi.Hot R):0≤‖x.part i.val‖+δ:=add_nonneg (norm_nonneg _) non
  have entry (p:(parts R).Mode)(i:Multi.Hot R):
      (∏j∈p.val.erase i,(‖x.part j.val‖+δ))≤T:=by
    calc _≤∏_j∈p.val.erase i,a:=prod_le_prod (fun j _=>xp j) (fun j _=>limit j.val)
         _=a^(p.val.erase i).card:=by simp
         _≤T:=pow_le_pow_right₀ one (card_le_univ _)
  have other (p:(parts R).Mode):others p.val (fun i=>‖x.part i.val‖+δ)≤p.val.card*T:=by
    change (∑i∈p.val,_)≤_
    exact (sum_le_sum fun i _=>entry p i).trans_eq (by simp)
  unfold cost count
  rw [Finset.sum_mul]
  refine (Finset.sum_le_sum (s:=shards R s) fun p _=>?_).trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (shards R s)) ?_)
  · exact (mul_le_mul_of_nonneg_left (other p) (norm_nonneg _)).trans_eq (by ring)
  · intros;have an:=zero_le_one.trans one;positivity

end YM.Integration.WilsonCoherentMayerPriorCapacity
