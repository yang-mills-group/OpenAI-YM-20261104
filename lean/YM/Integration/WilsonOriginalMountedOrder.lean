import YM.Integration.WilsonOriginalOrdinaryFaceOrder

/-! The finite partition amplification at a real original decoder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMountedOrder
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm Multi Push.AbsoluteSums.Animals
open WilsonRootedKioskOccupiedSlip WilsonOriginalOrdinaryFlatHulls
open WilsonOriginalSeparatedRegular WilsonOriginalSeparatedMask Comparison.Density.Transport
open scoped BigOperators Classical
open WilsonOriginalMountedRegular

variable {V:Type}[DecidableEq V]{J:Census V}

def width (s:J.Mode):ℕ:=s.val.card

theorem blocks (s:J.Mode)(q:(parts J).Mode)(hq:q∈shards J s):q.val.card ≤ width s:=by
  have united:unionOf q=s:=(chooses s q).mp hq
  calc
    q.val.card = ∑_∈q.val,1:=by simp
    _ ≤ ∑x∈q.val,x.sites.card:=sum_le_sum fun x _=>card_pos.mpr x.property
    _ = (unionOf q).val.card:=(card_biUnion (parts_wise _)).symm
    _ = width s:=by rw [united];rfl

variable {G:Gauge} {R:Run G}{i per:ℕ}[Fintype V]{vac:RG.Rep G (R.family.side i per)}
    {row:WilsonOriginalOccupiedWindow.Slice R J vac}{target:Config G (R.family.side i per)→Poly J}{s:J.Mode}

def event (F:Filing R vac row target s)(base:ℕ)(tol β spring:ℝ)(p:ℕ):ℝ:=
  let span:=max vac.p.B (reach vac.p.B F.h)
  if base=i then 0 else ((s.val.card*(span+span+1)^4:ℕ):ℝ)*(4*Real.exp (vac.p.supportExponent+2))*
    tol/β^p*(Real.exp spring)^2

theorem original (F:Filing R vac row target s)(base p D P:ℕ){tol β spring g:ℝ}
    (tp:0 ≤ tol)(bp:0 ≤ β)(gp:0<g)(gs:g ≤ 1)(debt:F.M ≤ (g^D)⁻¹)
    (small:F.W*F.rent+F.W*((Real.exp (F.α*F.h))⁻¹*F.gross)+F.δ ≤ g^(P+D*width s))
    (failed:event F base tol β spring p ≤ g^(P+D*width s)):
    F.bill base tol β spring p ≤ WilsonOriginalOrdinaryFaceOrder.constant s (width s)*g^P:=by
  have inc:∀t∈shards J s,t.val.card ≤ width s:=fun t ht=>blocks s t ht
  have light:0 ≤ F.W*F.rent+F.W*((Real.exp (F.α*F.h))⁻¹*F.gross)+F.δ:=
    add_nonneg (add_nonneg (mul_nonneg F.wallet_nn F.rent_nn)
      (mul_nonneg F.wallet_nn (mul_nonneg (inv_nonneg.mpr (Real.exp_nonneg _)) F.gross_nn))) F.delta_nn
  have probability:0 ≤ event F base tol β spring p:=by unfold event;split_ifs <;> positivity
  have norm:=WilsonOriginalOrdinaryFaceOrder.original s (width s) D P (le_refl _) inc gp gs F.M_nn
    debt light small probability failed
  unfold Filing.bill
  unfold event at norm
  by_cases edge:base=i
  · simpa only [if_pos edge,mul_zero,add_zero] using norm
  · simpa only [if_neg edge,mul_assoc,div_eq_mul_inv] using norm

end YM.Integration.WilsonOriginalMountedOrder
end
