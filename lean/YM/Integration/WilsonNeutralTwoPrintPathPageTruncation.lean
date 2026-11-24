import YM.Integration.WilsonNeutralTwoPrintPathPageLedger
import YM.Integration.WilsonNeutralTwoPrintPathRankFare
import YM.Integration.WilsonOriginalRelativePageIncome
import YM.Integration.WilsonPointChildDeckAngular
import YM.Integration.WilsonPointChildRelativeLift

/-! Absolute angular invoices for the genuine separate copies of an occupied family,
on a single enlarged lattice, after fixing one copy of its root. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathPageTruncation
open Function Finset Lattice Laurent Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained locate)
open WilsonPointChildRelativeLift (centers)
open WilsonPointChildDeckAngular (window)
open UVNext.PricedKernels
open scoped BigOperators Classical
open private spent from YM.Integration.WilsonNeutralTwoPrintPathRankFare
variable {V α ι:Type} [NormedAddCommGroup V][NormedSpace ℝ V][Fintype α]{n X:Side}{r:ℕ}


open WilsonNeutralTwoPrintPathPageLedger (price)
variable [DecidableEq ι]

theorem original (h:n.val∣X.val)(J:Finset ι)(a:ι)(live:a∈J)(root:Site X)(site:(J.erase a)→Site X)
    (σ A:ℝ)(hs:0<σ)(test:V →L[ℝ] ℂ)
    (K:((J.erase a)→Fin (Pages n X))→Ten V (Site X × α) r)
    (gross:∀p,Wig (tor X) (wrap X ∘ toe J a (lift root) (centers h J a root site p)) σ A J (K p))
    (D:ℕ):
    (∑p∈Finset.univ.filter (fun p=>∃i:J.erase a,D≤ separation root (locate h site p i)),
      ∑x:Fin r→Site X × α,‖test (K p x)‖) ≤
      Real.exp (-((σ/2)/2)*(D:ℝ))*price J a α r σ (‖test‖*A):=by
  let span:=fun p (x:Fin r→Site X × α)=>
    (Syn (tor X) (wrap X ∘ toe J a (lift root) (centers h J a root site p)) J x:ℝ)
  let far:=fun p:(J.erase a)→Fin (Pages n X)=>∃i:J.erase a,D≤ separation root (locate h site p i)
  let B:=∑i:J.erase a,separation root (site i)
  have seats(i:J.erase a):separation root (site i)≤B:=
    Finset.single_le_sum (fun i (_:i∈Finset.univ)=>Nat.zero_le (separation root (site i))) (Finset.mem_univ i)
  have budget:=(WilsonNeutralTwoPrintPathPageLedger.original h J a live root site B (fun i=>Nat.cast_le.mpr (seats i)) σ A hs test K gross).1
  have one (p) (f:far p) (x:Fin r→Site X × α):‖test (K p x)‖ ≤
      Real.exp (-((σ/2)/2)*(D:ℝ))*(Real.exp ((σ/2)/2*span p x)*‖test (K p x)‖):=by
    obtain ⟨i,hit⟩:=f
    have reaches:=WilsonPointChildRelativeLift.connected h J a live root site r p x i
    have compare:(D:ℝ)≤ span p x:=Nat.cast_le.mpr (hit.trans reaches)
    have attr:1≤Real.exp (-((σ/2)/2)*(D:ℝ))*Real.exp ((σ/2)/2*span p x):=by
      rw [←Real.exp_add,Real.one_le_exp_iff]
      nlinarith
    simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right attr (norm_nonneg (test (K p x)))
  calc
    _ ≤ ∑p∈Finset.univ.filter far,Real.exp (-((σ/2)/2)*(D:ℝ))*
        (∑x:Fin r→Site X × α,Real.exp ((σ/2)/2*span p x)*‖test (K p x)‖):=by
      apply Finset.sum_le_sum
      intro p hit
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun x _=>one p (Finset.mem_filter.1 hit).2 x)
    _ = Real.exp (-((σ/2)/2)*(D:ℝ))*
        (∑p∈Finset.univ.filter far,∑x:Fin r→Site X × α,Real.exp ((σ/2)/2*span p x)*‖test (K p x)‖):=by
      rw [Finset.mul_sum]
    _ ≤ _:=by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply le_trans _ budget
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _=>Finset.sum_nonneg
        (fun x _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))

end YM.Integration.WilsonNeutralTwoPrintPathPageTruncation
end
