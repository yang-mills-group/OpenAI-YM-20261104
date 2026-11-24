import YM.Integration.WilsonCapturedOriginalClockTaylor
import YM.QuadraticLocal.Rebirth.Vacuum
import YM.FVAAlt2.Booth.Prices

/-! Read the genuine deposited quiet field on its recorded incoming coupling, including its scalar. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedOriginalGrantClock
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Adjacent PertExtension.Series AllOrder
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker AllOrder.Laplace Primitives.TwoWave.RealSlice
open QuadraticLocal.Faith Stationary WilsonCoeffUV WilsonCoeffUV.Bank RegulatorIR RegulatorIR.FVAAlt2
open Booth RegulatorIR.Prim PositionX.Jet WilsonOriginalGaussianFieldPhase WilsonCapturedOriginalClockTaylor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{V:Type} [DecidableEq V] {J:Marker.Census V}
  (P:PathData G)(p:Clip)(π:Layout G)(T:Finset Age)(D:Bulk.Colors J G n)
  (Q:Pace.Coin)(hQ:Q 0=0)(r:ℕ)
set_option quotPrecheck false
local notation "C"=> (QuadraticLocal.Rebirth.caliber Q hQ).direct r
local notation "F"=> WilsonOriginalGaussianFieldPhase.field (n:=n) P p π T
local notation "Z"=> QuadraticLocal.Fk.grant π T D

theorem evaluation (A:fieldDir G n 1):
    Gala.feeAct p P C Z A =ᶠ[𝓝 0] fun t=>Ribbon.fees C t*F (ray C A t):=by
  filter_upwards [(C).bright] with t ht
  let U:=represent (t • A)
  have eq:F (ray C A t)=mainTerm p P U+((C).enter t)^2*Precision.loop P U+(Z).vac ((C).enter t) U:=by
    change Floe.audition P p π T ((C).enter t) (represent (arm G n 1 ((arm G n 1).symm (t • A))))=_
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  change Ribbon.fees C t*(mainTerm p P U+(Z).vac ((C).enter t) U)+t^2 *Precision.loop P U=_
  rw [eq]
  have h:Ribbon.fees C t*((C).enter t)^2=t^2:=by
    unfold Ribbon.fees UnitCost.enter
    rw [mul_pow]
    field_simp
  linear_combination -Precision.loop P U *h

/-- The term at rank zero of the entire deposited action is retained explicitly. -/
def offset (e:ℕ):ℝ:=coeff (e+2) (Prim.tale (fun t=>Ribbon.fees C t*F 0))
variable {P p} {α K β:ℝ} (bounded:P.Bounds p α K β) (legal:Legal T π)

include bounded legal

theorem headed (A:fieldDir G n 1):
    radial C F r A = Spirit.glance r (Pace.grouping 0 π T p P) C ((arm G n 1).symm A):=by
  funext t
  unfold radial Spirit.glance delay
  apply sum_congr rfl
  intro i _
  change (C).enter t^i*Assembly.jet F (i+2) (1,((C).rating t)⁻¹ • A)=
    (C).enter t^i*Pace.grouping 0 π T p P i n (((C).rating t)⁻¹ • (arm G n 1).symm A)
  rw [WilsonOriginalGaussianFieldPhase.linked bounded π T legal,map_smul]

theorem original (simple:G.Simple)(A:fieldDir G n 1){e:ℕ}(he:e≤r):
    coeff (e+2) (Prim.tale (Gala.feeAct p P C Z A))=
      offset (n:=n) P p π T Q hQ r e+Pace.grouping Q π T p P e n ((arm G n 1).symm A):=by
  let x:=(arm G n 1).symm A
  let g:=Spirit.glance r (Pace.grouping 0 π T p P) C x
  have compatible:=Spirit.auth Q hQ r P p π T
  have enrolled:Act r g (fun i=>Pace.grouping Q π T p P i n x):=compatible n x
  let L:ℝ×fieldDir G n 1 →L[ℝ] ℝ×Link G n:=(ContinuousLinearMap.fst ..).prod
    ((arm G n 1).symm.toContinuousLinearMap ∘L ContinuousLinearMap.snd ..)
  have smooth:ContDiffAt ℝ ω F 0:=by
    apply ContDiffAt.comp (g:=Costume.evaluation (n:=n) P p T π) (f:=L) _ _ L.contDiff.contDiffAt
    simpa only [map_zero] using WilsonOriginalGaussianFieldPhase.smooth (n:=n) bounded π T legal
  have phase:=WilsonCapturedOriginalClockTaylor.issued C F r smooth
    (WilsonOriginalGaussianFieldPhase.first simple bounded π T legal) A (k:=e+2) (by omega)
  have regrade:=headed π T Q hQ r bounded legal A
  rw [regrade] at phase
  have fee:ContDiffAt ℝ ω (Ribbon.fees C) 0:=((C).smooth.pow _).inv (by simp [(C).origin])
  let scalar:ℝ→ℝ:=fun t=>Ribbon.fees C t*F 0
  have hs:ContDiffAt ℝ ω scalar 0:=fee.mul contDiffAt_const
  have hg:ContDiffAt ℝ ω ((fun t:ℝ=>t^2)*g) 0:= (contDiffAt_id.pow 2).mul enrolled.nice
  have here: coeff (e+2) (Prim.tale (Gala.feeAct p P C Z A))=
      Assembly.jet (fun t=>Ribbon.fees C t*F (ray C A t)) (e+2) 1:=by
    rw [Prim.tale_jet]
    exact congrArg (fun z=>((e+2).factorial:ℝ)⁻¹ • z (fun _=>1))
      ( (evaluation P p π T D Q hQ r A).iteratedFDeriv ℝ (e+2)).eq_of_nhds
  rw [here,phase]
  change Radial.jet (scalar+(fun t:ℝ=>t^2)*g) (e+2) 1=_
  rw [←Prim.tale_jet,Prim.tale_add (hs.of_le le_top) (hg.of_le le_top),map_add,Prim.tale_mul (f:=fun t:ℝ=>t^2) (g:=g) (contDiffAt_id.pow 2) (enrolled.nice.of_le le_top),
    Script.dictates (f:=fun t:ℝ=>t^2) (contDiffAt_id.pow _) (Script.predicts_pow _),
    coeff_X_pow_mul',if_pos (by omega),show e+2-2=e by omega]
  congr 1
  rw [Prim.tale_jet]
  exact (show Assembly.jet g e 1=someJ g e by rw [someJ,iteratedDeriv_eq_iteratedFDeriv]).trans
    (enrolled.writes e he)

end YM.Integration.WilsonCapturedOriginalGrantClock
end
