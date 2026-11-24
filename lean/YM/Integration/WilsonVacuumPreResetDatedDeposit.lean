import YM.Integration.WilsonVacuumPreResetMassCall

/-! One gallery serves as an original input and a deposited output at successive dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDatedDeposit
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)

open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice

structure Issued (N j e:ℕ)(Z:SeriesA G)(σ C:ℝ):Prop where
  positive:0<σ
  lower:∀a∈Z,3≤a.grade
  upper:fromBefore Z (3+e)
  size:Z.length ≤ meterPre (3+e)
  purchase:Draw Z σ C
  cover:∀i<3+e,(breast (R.alloy.B.kin.path N j) ((levels R).params j).clip+ sandLift Z) i=
    actionW (levels R) (ratio R) N j i
  periodic:∀i<3+e,∀n:Side,∀l,(front (R.alloy.B.kin.path N j) ((levels R).params j).clip n+sands Z n) i (l+1)=
    lagoon (actionW (levels R) (ratio R) N j i (l+1)) n

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃ W:Credit,∀ᶠ j:ℕ in atTop,∃σ:ℝ,0<σ ∧ σ⁻¹≤zz (levels R) j ∧
      ∀N:ℕ,j≤N→∃Z:SeriesA G,Issued R N j e Z σ (W.buy (zz (levels R) j)+zz (levels R) j*(levels R).clock.loopCap j):=by
  obtain ⟨W,dates⟩:=FundedOriginalVacuumPaths.corrections R simple v rows paths e
  refine ⟨W,?_⟩
  filter_upwards [dates] with j booked
  obtain ⟨floor,positive,steep,works⟩:=booked
  refine ⟨_,positive,steep,?_⟩
  intro N top
  obtain ⟨Z,lo,hi,count,bill,cells⟩:=works N top
  exact ⟨Z,positive,lo,hi,count,bill,fun i hi=>(cells i hi).1,fun i hi=>(cells i hi).2⟩

theorem call (simple:G.Simple){N j e:ℕ}(hj:j<N){Z Z':SeriesA G}{σ C σ' C':ℝ}
    (lo:Issued R N j e Z σ C)(hi:Issued R N (j+1) e Z' σ' C'):
    MassCall R hj (bank Z') (bank Z)
       (PertExtension.Series.Tested.term (pitch (levels R) (ratio R) N j-1)) e:=by
  apply WilsonVacuumPreResetMassCall.binding R simple hj Z Z'
  · intro t test c z w
    have proper:LocalRatio R.metals.O:=(RunFormalChain.fromRun R).receipt
    have unit:=Bank.angle_tilt (A:=levels R) simple proper hj
    have link (x:rule (Coarse G) c):=WilsonVacuumPreResetTorusRegradedAction.original
      _ unit (R.alloy.B.kin.path N j) ((levels R).params j).clip Z lo.positive lo.purchase lo.lower test x
    dsimp only
    rw [link z,link w]
    apply WilsonVacuumPreResetTorusCoverAction.original R simple hj Z c _ z w
    intro l
    exact WilsonLimitConstruction.FundedSpringPeriodRows.regraded R simple N j hj c _ t l
      (fun i bound=>lo.periodic i (by omega) c l)
  · intro p F tag T _ _ J Q x y t ht _
    let U:=filed R N j p Z'
    let E:=covered R N j p
    have kp:(income R N j p).path=R.alloy.B.kin.path N (j+1):=(RunFormalChain.fromRun R).selected N p (j+1) hj
    have kb:(income R N j p).clip=((levels R).params (j+1)).clip:=(RunFormalChain.fromRun R).clips N p (j+1) hj
    have filedRows (a:ℕ)(ha:a<3+e)(l:ℕ):U a (l+1)=E a (l+1):=by
      unfold U filed
      rw [kp,kb]
      exact hi.periodic a ha (fine R j p) l
    have head:=WilsonVacuumPreResetDepositedPhase.head R N j p hj Z' simple (filedRows 0 (by omega))
    have price (a:ℕ)(ha:a<3+e):coeff a (Blue.flash U-Blue.flash E)=
        MvPolynomial.C (MvPolynomial.eval 0 (coeff a (Blue.flash U-Blue.flash E))):=
      WilsonVacuumPreResetFoldedInlet.fieldIndependent U E a
        (WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _) (filedRows a ha)
    exact WilsonVacuumPreResetOriginalOutput.original R N j p hj F tag Z' head Q ((levels R).budget (j+1))
      (e+2) hi.positive hi.purchase hi.lower (fun a ha=>by have h:=hi.upper a ha; omega) simple (3+e) price x y (e+2) t ht (by omega)

end YM.Integration.WilsonVacuumPreResetDatedDeposit
