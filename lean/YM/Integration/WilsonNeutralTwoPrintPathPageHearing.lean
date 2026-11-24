import YM.Integration.WilsonNeutralTwoPrintPathPageRead
import YM.Integration.WilsonNeutralTwoPrintPathPageReturn
import YM.Integration.WilsonNeutralTwoPrintPathPageLedger
import YM.Integration.WilsonOriginalRelativePageIncome
import YM.Integration.WilsonPointChildDeckAngular
import YM.Integration.WilsonPointChildRelativeLift

/-! Absolute angular invoices for the genuine separate copies of an occupied family,
on a single enlarged lattice, after fixing one copy of its root. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathPageHearing
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
      MarkU y J (K p) (F y) σ A)
    (weights:(Fin r→Site n × α)→ℂ)(height:ℝ)(positive:0 ≤ height)(bounded:∀v,‖weights v‖ ≤ height):
    let chosen:=toe J a (lift root) (centers h J a root site (retained h site))
    let C:=price J a α r σ (‖test‖*A)
    ‖(∑x:Fin r→Site X × α,(∑p,test (K p x))*weights (WilsonNeutralTwoPrintPathPageRead.lower h ∘ x))-
        ∑y:Fin r→Site n × α,test (plume (F chosen) n y)*weights y‖ ≤
      (Real.exp (-(((σ/2)/2)*((n.val:ℝ)-D))/2)*C+‖test‖*(tariff α r σ A*catchW (σ/512) X))*height:=by
  intro chosen C
  have sp:Summable (fun z=>‖F chosen z‖):=
    keg ((gross (retained h site)).access.to_cork hs.le live) hs
  have equal:=WilsonNeutralTwoPrintPathPageRead.held h (F chosen) sp test weights
  rw [←equal,←Finset.sum_sub_distrib]
  have rate:=WilsonNeutralTwoPrintPathPageReturn.original h J a live root site D near room σ A hs test K F gross
  calc
    _ ≤ ∑x:Fin r→Site X × α,‖((∑p,test (K p x))-test (plume (F chosen) X x))*
            weights (WilsonNeutralTwoPrintPathPageRead.lower h ∘ x)‖:=by
      simp_rw [sub_mul]
      exact norm_sum_le _ _
    _ ≤ ∑x:Fin r→Site X × α,‖(∑p,test (K p x))-test (plume (F chosen) X x)‖*height:=by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)
    _ ≤ _:=by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right rate positive

end YM.Integration.WilsonNeutralTwoPrintPathPageHearing
end
