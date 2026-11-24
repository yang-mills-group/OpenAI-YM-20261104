import YM.Integration.WilsonNeutralTwoPrintPathPageHearing
import YM.Integration.WilsonNeutralTwoPrintPathPeriodFloor

/-! A single physically held angular reading on a fixed relative configuration,
before summing configurations or taking the enhanced-period limit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathCofinalPeg
open Filter Function Finset Lattice Wilson
open RG WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Mer WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Realm
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonNeutralTwoPrintPathPageRead (lower)
open scoped Classical BigOperators Topology
variable {V ι α:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V][Fintype α]
variable {r:ℕ}{n X:Side}
def read (h:n.val∣X.val)(P:Ten V (Site X × α) r)(F:Ten V (Cloth α) r)(test:V →L[ℝ] ℂ)
    (weights:(Fin r→Site n × α)→ℂ):ℂ:=
  (∑x:Fin r→Site X × α,test (P x)*weights (lower h ∘ x))-
    ∑x:Fin r→Site n × α,test (plume F n x)*weights x

theorem original (h:n.val∣X.val)(y:ι → Cover)(J:Finset ι)(a:ι)(live:a∈J)
    {σ A:ℝ}(strip:0<σ)(P:Ten V (Site X × α) r)(F:Ten V (Cloth α) r)(test:V →L[ℝ] ℂ)
    (paid:MarkU y J P F σ A)(room:4*crestCard y J<X.val)
    (weights:(Fin r→Site n × α)→ℂ)(height:ℝ)(hh:0≤height)(bounded:∀x,‖weights x‖ ≤ height):
    ‖read h P F test weights‖ ≤ (‖test‖*height*tariff α r σ A)*catchW (σ/512) X:=by
  have summable:Summable (fun z=>‖F z‖):=keg (paid.access.to_cork strip.le live) strip
  have same:=WilsonNeutralTwoPrintPathPageRead.held h F summable test weights
  have paidSum:=WilsonNeutralTwoPrintPathRankFare.original (n:=X) ⟨a,live⟩ room strip paid
  unfold read
  rw [←same,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑x:Fin r→Site X × α,‖(test (P x)-test (plume F X x))*weights (lower h ∘ x)‖:=by
      simp_rw [sub_mul]
      exact norm_sum_le _ _
    _ ≤ ∑x:Fin r→Site X × α,(‖test‖*height)*‖P x-plume F X x‖:=by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul,←test.map_sub]
      calc
        _ ≤ (‖test‖*‖P x-plume F X x‖)*height:=
          mul_le_mul (test.le_opNorm _) (bounded _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = _:=by ring
    _ ≤ _:=by
      rw [←Finset.mul_sum]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left paidSum (mul_nonneg (norm_nonneg _) hh)

theorem disappears (σ C:ℝ)(strip:0<σ):
    Tendsto (fun n:ℕ=>C*catchW (σ/512) n) atTop (𝓝 0):=by
  have step:Tendsto (fun n:ℕ=>σ/512*(n:ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have wash:=Real.tendsto_exp_neg_atTop_nhds_zero.comp step
  simpa only [catchW,Function.comp_apply,neg_mul,mul_zero] using
    (tendsto_const_nhds (x:=C)).mul wash

end YM.Integration.WilsonNeutralTwoPrintPathCofinalPeg
end
