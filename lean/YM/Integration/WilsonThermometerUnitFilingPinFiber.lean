import YM.Integration.WilsonThermometerUnitFilingPinCharge

/-! Absolute summation on the actual signed fiber of a finite inversion deck. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinFiber
open Function Filter RegulatorIR Geometry Taping Budget Budget.Packet Budget.Tuple
open scoped Classical ENNReal BigOperators Topology

variable {I X Y:Type}{P:ℝ}{r:ℕ}(A:Deck P X Y)(f:I→Packet X r)

private theorem joint {pay:I→ℝ}(positive:∀ i,0 ≤ pay i)(paid:Summable pay)
    (wage:∀ i,quota (f i) 1 ≤ ENNReal.ofReal (pay i))(y:Tuple Y r):
    Summable (fun p:I×Stalk A.project y=>A.dyed (f p.1) p.2.val):=by
  apply quota_summable (w:=1) (fun _=>le_rfl)
  have entire:(∑' i, ENNReal.ofReal (pay i))≠⊤:=by
    rw [← ENNReal.ofReal_tsum_of_nonneg positive paid];exact ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top entire
  unfold quota
  simp only [Pi.one_apply,mul_one]
  rw [ENNReal.tsum_prod (f:=fun i (x:Stalk A.project y)=>‖A.dyed (f i) x.val‖ₑ)]
  apply ENNReal.tsum_le_tsum
  intro i
  simp only [A.dyed_cost]
  apply (ENNReal.tsum_comp_le_tsum_of_injective (@Subtype.val_injective _ (fun v:Tuple X r=>A.project v=y))
    (fun v=>‖f i v‖ₑ)).trans
  simpa only [quota,Pi.one_apply,mul_one] using wage i

theorem original {pay:I→ℝ}(positive:∀ i,0 ≤ pay i)(paid:Summable pay)
    (wage:∀ i,quota (f i) 1 ≤ ENNReal.ofReal (pay i))(y:Tuple Y r):
    HasSum (fun i=>A.scroll (f i) y) (A.scroll (fun v=>∑' i,f i v) y):=by
  let g (i:I)(x:Stalk A.project y):=A.dyed (f i) x.val
  have hg:Summable (Function.uncurry g):=joint A f positive paid wage y
  change HasSum (fun i=>∑' x,g i x) (∑' x:Stalk A.project y,(∑' i,f i x.val)*A.polish x.val)
  have same:(∑' i,∑' x,g i x) = ∑' x:Stalk A.project y,(∑' i,f i x.val)*A.polish x.val:=by
    rw [← hg.tsum_comm]
    apply tsum_congr
    intro x
    exact tsum_mul_right
  rw [← same]
  exact hg.prod.hasSum

theorem finite {pay:I→ℝ}(positive:∀ i,0 ≤ pay i)(paid:Summable pay)
    (wage:∀ i,quota (f i) 1 ≤ ENNReal.ofReal (pay i))(s:Finset I)(y:Tuple Y r):
    A.scroll (∑ i∈s,f i) y = ∑ i∈s,A.scroll (f i) y:=by
  have h:=joint A f positive paid wage y
  unfold Deck.scroll Stalk.collect Deck.dyed
  simp only [Finset.sum_apply,Finset.sum_mul]
  exact Summable.tsum_finsetSum fun i _=>h.prod_factor i

end YM.Integration.WilsonThermometerUnitFilingPinFiber
