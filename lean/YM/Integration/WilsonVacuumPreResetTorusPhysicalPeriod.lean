import YM.Integration.WilsonVacuumPreResetTorusMaterial

/-! A common fundamental period for all physical cutoffs at one original date.
All the finite conditionals below use the deposited prior at that date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusPhysicalPeriod
open AllOrder AllOrder.Floe AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Classical Topology BigOperators

open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port PhysicalNext.Repeat.Legato FVA1Physical.MixedResets
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero Comparison.RG02

open WilsonVacuumPreResetTorusRegister WilsonVacuumPreResetTorusMaterial
open Comparison.RG02.Order Next.SectorChange Marker Exterior
variable {G:Gauge}(R:Run G)
variable {r:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
variable {Q:r.Tab R.rolls}

def base (S:Schedule)(j:ℕ):Side:=(4:Side)*S.denominator j
def copies (S:Schedule)(per:ℕ):ℕ:=((S.period per).val/4)^4

private theorem length (S:Schedule)(j per:ℕ):
    (S.side j per).val=(base S j).val*((S.period per).val/4):=by
  change (S.period per).val*(S.denominator j).val=(4*(S.denominator j).val)*_
  have h:=Nat.mul_div_cancel' (S.period_four per)
  calc
    _=(4*((S.period per).val/4))*(S.denominator j).val:=by rw [h]
    _=_:=by ring

def window (S:Schedule)(j per:ℕ):Macrame.Window (base S j) (S.side j per) (copies S per):=
  Macrame.normal ⟨_,length S j per⟩ (length S j per)

def held (N j k:ℕ)(π:ℕ→Layout G)(per:ℕ)(live:j<N)
    (Y:Forest (R.alloy.B.a.clock.op j per).ratio)(tag:(R.alloy.B.a.clock.op j per).Choices)
    (t:ℕ)(z:rule (Coarse G) (R.family.side j per)):ℂ:=
  let angle:=physicalAngle (R.family.side j per) z
  let data:=QuadraticLocal.Fk.grant (π (j+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
    (Bulk.Colors.noHole G (R.family.side (j+1) per) unmarked)
  Comparison.RG02.Laplace.detail
    (logVac (PhysicalWilsonPeriodizedMaterial.reference R N j per live angle data (Burn.horizon k+2)))
    unmarked.quiet t + if t=0 then Symmetry.price ((RunFormalChain.fromRun R).step N j per live) Y tag angle else 0

theorem original {N b j k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (path:PlanV.Path r R.alloy Q (Burn.horizon k) N b π Γ)(early:b≤j)(live:j<N)
    (F:∀per,Forest (R.alloy.B.a.clock.op j per).ratio)
    (tag:∀per,(R.alloy.B.a.clock.op j per).Choices){t:ℕ}(valid:t≤Burn.horizon k+2)
    (z w:rule (Coarse G) (base R.family.S j)):
    let s:=R.family.S
    let filed:=WilsonVacuumPreResetTorusRepriced.Reading R N j k π Γ t (base s j)
    ((filed z-filed w:ℝ):ℂ)=earlier R N j k π t w-earlier R N j k π t z ∧
    Tendsto (fun p=>(copies s p:ℝ)⁻¹ •
        (held R N j k π p live (F p) (tag p) t (convey (window s j p) w)-
         held R N j k π p live (F p) (tag p) t (convey (window s j p) z)))
      atTop (𝓝 ((filed z-filed w:ℝ):ℂ)):=by
  intro s filed
  have report:=WilsonVacuumPreResetTorusRegister.original R path j early live valid (base s j) z w
  have large:Tendsto (fun p=>(s.side j p).val) atTop atTop:=by
    apply tendsto_atTop_mono (f:=fun p=>(s.period p).val) _ s.period_strict.tendsto_atTop
    intro p
    exact Nat.le_mul_of_pos_right _ (s.denominator j).property
  have many (p:ℕ):0<copies s p:=by
    have h:=s.period_four p
    have hp:0<(s.period p).val:=(s.period p).property
    have pos:0<(s.period p).val/4:=by omega
    exact pow_pos pos _
  refine ⟨report.1,(report.2 _ _ (window s j) many large).congr' (Eventually.of_forall fun p=>?_)⟩
  unfold tileAt
  dsimp only
  rw [smul_sub]
  congr 1 <;> apply congrArg (fun a:ℂ=>(copies s p:ℝ)⁻¹ • a) <;>
    exact WilsonVacuumPreResetTorusMaterial.original R path early live p (F p) (tag p) _ valid

end YM.Integration.WilsonVacuumPreResetTorusPhysicalPeriod
