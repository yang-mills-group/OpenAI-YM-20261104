import YM.Integration.WilsonNeutralTwoPrintPathPageLedger
import YM.Integration.WilsonOriginalRelativePageIncome
import YM.Integration.WilsonPointChildDeckAngular
import YM.Integration.WilsonPointChildRelativeLift

/-! Absolute angular invoices for the genuine separate copies of an occupied family,
on a single enlarged lattice, after fixing one copy of its root. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathPageReturn
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
variable {V α ι:Type} [NormedAddCommGroup V][NormedSpace ℝ V][Fintype α]{n X:Side}{r:ℕ}

open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
variable [DecidableEq ι][CompleteSpace V]

theorem original (h:n.val∣X.val)(J:Finset ι)(a:ι)(live:a∈J)(root:Site X)
    (site:(J.erase a)→Site X)(D:ℕ)(near:∀v,separation root (site v) ≤ D)
    (room:32*D < X.val)(σ A:ℝ)(hs:0<σ)(test:V →L[ℝ] ℂ)
    (K:((J.erase a)→Fin (Pages n X))→Ten V (Site X × α) r)
    (F:(ι → Cover)→Ten V (Cloth α) r)
    (gross:∀p,let y:=toe J a (lift root) (centers h J a root site p)
      MarkU y J (K p) (F y) σ A):
    let retainedSites:=toe J a (lift root) (centers h J a root site (retained h site))
    let C:=price J a α r σ (‖test‖*A)
    (∑x,‖(∑p,test (K p x))-test (plume (F retainedSites) X x)‖) ≤
      Real.exp (-(((σ/2)/2)*((n.val:ℝ)-D))/2)*C+
        ‖test‖*(tariff α r σ A*catchW (σ/512) X):=by
  intro y C
  let keep:=retained h site
  have apart:4*crestCard y J < X.val:=by
    have c:=WilsonPointChildRelativeLift.radius h J a root site D near
    dsimp only at c
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 4 c) (by omega)
  have shell:=WilsonNeutralTwoPrintPathRankFare.original ⟨a,live⟩ apart hs (gross keep)
  have tails:=(WilsonNeutralTwoPrintPathPageLedger.original h J a live root site D
    (fun v=>Nat.cast_le.mpr (near v)) σ A hs test K (fun p=>(gross p).bill)).2
  have stripped:
      (∑x,‖(∑p,test (K p x))-test (K keep x)‖) ≤
        Real.exp (-(((σ/2)/2)*((n.val:ℝ)-D))/2)*C:=by
    apply le_trans _ tails
    apply sum_le_sum
    intro x _
    apply le_mul_of_one_le_left (norm_nonneg _)
    apply Real.one_le_exp
    have pos:0 ≤ window root x:=Nat.cast_nonneg _
    positivity
  calc
    _ ≤ ∑x,(‖(∑p,test (K p x))-test (K keep x)‖+‖test (K keep x)-test (plume (F y) X x)‖):=by
      apply sum_le_sum
      intro x _
      simpa only [←dist_eq_norm] using dist_triangle (∑p,test (K p x)) (test (K keep x)) (test (plume (F y) X x))
    _ ≤ _:=by
      rw [sum_add_distrib]
      apply add_le_add stripped
      calc
        _ ≤ ∑x,‖test‖*‖K keep x-plume (F y) X x‖:=by
          apply sum_le_sum
          intro x _
          rw [←map_sub]
          exact test.le_opNorm _
        _ ≤ _:=by
          rw [←mul_sum]
          exact mul_le_mul_of_nonneg_left shell (norm_nonneg _)

end YM.Integration.WilsonNeutralTwoPrintPathPageReturn
end
