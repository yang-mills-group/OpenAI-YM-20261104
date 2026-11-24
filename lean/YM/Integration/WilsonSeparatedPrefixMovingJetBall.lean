import Mathlib.Topology.ContinuousMap.Bounded.Normed
import YM.Integration.WilsonSeparatedPrefixMovingJointFarBook
import YM.Integration.WilsonSeparatedPrefixMovingJointPartial
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of the signed physical test before the native vote. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJetBall
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingAddressInk (writer)


open MeasureTheory Set
open scoped ContDiff
variable {Ω:Type*}[MeasurableSpace Ω]{μ:Measure Ω}
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
abbrev UnitJet (D:ℕ):=Metric.closedBall (0:Volume D) 1
abbrev Bank (D:ℕ):=BoundedContinuousFunction (UnitJet D) ℝ
theorem unit (u:UnitJet D):‖u.val‖≤1:=mem_closedBall_zero_iff.mp u.property
def note (L:Vote D):Bank D:=BoundedContinuousFunction.mkOfBound 
  ⟨fun u:UnitJet D=>L u.val,L.continuous.comp continuous_subtype_val⟩ (‖L‖+‖L‖) (fun x y=>by
    rw [dist_eq_norm]
    calc
      _≤‖L x.val‖+‖L y.val‖:=norm_sub_le .. 
      _≤‖L‖*1+‖L‖*1:=add_le_add ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (unit x) (norm_nonneg L)))
        ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (unit y) (norm_nonneg L)))
      _= _:=by ring)
def register (D:ℕ):Vote D→L[ℝ]Bank D:=LinearMap.mkContinuous
  (⟨⟨note,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩,fun _ _=>BoundedContinuousFunction.ext fun _=>rfl⟩:Vote D→ₗ[ℝ]Bank D) 1
  (fun L=>by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg L)).mpr
    intro u
    change ‖L u.val‖≤‖L‖
    simpa only [mul_one] using (L.le_opNorm u.val).trans (mul_le_mul_of_nonneg_left (unit u) (norm_nonneg L)))
def sterling (D:ℕ):ℝ→L[ℝ]Bank D:=LinearMap.mkContinuous
  (⟨⟨BoundedContinuousFunction.const _,fun _ _=>rfl⟩,fun _ _=>rfl⟩:ℝ→ₗ[ℝ]Bank D) 1
  (fun t=>by change ‖BoundedContinuousFunction.const (UnitJet D) t‖≤1*‖t‖;rw [one_mul];exact BoundedContinuousFunction.norm_const_le _)
def inspect (u:UnitJet D):Bank D→ₐ[ℝ]ℝ where
  toFun:=fun f=>f u
  map_one':=rfl
  map_mul' _ _:=rfl
  map_zero':=rfl
  map_add' _ _:=rfl
  commutes' _:=rfl
def reading (u:UnitJet D):Bank D→L[ℝ]ℝ:=BoundedContinuousFunction.evalCLM ℝ u
theorem original (u:UnitJet D)(L:Vote D)(a:ℝ):
    reading u (register D L)=L u.val ∧ reading u (sterling D a)=a ∧
    ∀f:Bank D,reading u f=inspect u f∧‖reading u f‖≤‖f‖:=by
  exact ⟨rfl,rfl,fun f=>⟨rfl,f.norm_coe_le_norm u⟩⟩
end YM.Integration.WilsonSeparatedPrefixMovingJetBall
