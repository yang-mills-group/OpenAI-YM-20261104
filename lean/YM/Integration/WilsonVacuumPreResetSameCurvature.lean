import YM.Integration.WilsonVacuumPreResetCurvatureCharge
import YM.Integration.WilsonVacuumPreResetSameTime
import YM.Integration.WilsonVacuumPreResetPrecursorReserve
import YM.Integration.WilsonVacuumPreResetFiledQuote
import YM.Integration.WilsonPhysicalHistoryRetainedSpringPitchSubpower

/-! The exact quadratic, cubic and quartic source tariff on the incoming
physical date is uniformly absorbed by the original reset forecast. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetSameCurvature
open Filter Lattice RG Wilson WilsonStartup AnalyticBridge VerifiedReset Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Fk PhysicalNext.Repeat.Legato WilsonLimitConstruction IterationFour.Vacuum
open WilsonVacuumPreResetPeriodEntries WilsonVacuumPreResetRenderRank
open scoped Topology BigOperators Classical
variable {G:Gauge}


theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (issued:WilsonVacuumPreResetPrecursorReserve.Issued R.kit)
    (time:RG01Estimate.Chart.Barrier R.alloy (fun _ i=>((i:ℝ)+1)⁻¹))(r:ℕ){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,m<N→let j:=m
      let g:=regulatorRun R.family N per m
      let γ:=g^2*OriginalMarkedRunAction.pitchTail R N j r g
      let β:=γ+R.alloy.B.kin.alpha N j
      let T:=V.params m
      let D:=V.params j
      ∀B:BudgetPoint,B.order=T.order→B.power=T.power→B.supportExponent≤T.supportExponent+6→
        B.threshold=(V.budget m).threshold→
        |WilsonVacuumPreResetCurvaturePrice.cost (G:=G) B D.clip D.width D.paths γ β| ≤ε*Time.forecastE V m:=by
  intro V
  let η:ℝ:=1/20
  have eta:0<η:=by norm_num [η]
  let M:ℝ:=(r-2+1:ℕ)
  have mp:0≤M:=by dsimp [M];positivity
  let f:=WilsonVacuumPreResetCurvatureCharge.factor η
  have fp:0≤f:=by dsimp [f,WilsonVacuumPreResetCurvatureCharge.factor];positivity
  let C:=f*(20*(M+1))
  have cp:0≤C:=by dsimp [C];positivity
  let W:Credit:=⟨1,1,le_rfl⟩
  filter_upwards [WilsonVacuumPreResetSameIncome.original R simple W eta,
    OriginalMarkedRunAction.pitch_subpower R simple v rows r eta,
    WilsonVacuumPreResetSameTime.original R simple time C cp ep] with m thermal pitches clock
  intro N per later j g γ β T D B ho hp hs ht
  obtain ⟨gp,one,_,theta,band⟩:=thermal N per (by omega)
  obtain ⟨alpha,_,tail⟩:=pitches N later per
  let A:=g^(-η)
  have ab:1≤A:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos gp one (neg_nonpos.mpr eta.le)
  have ip:WilsonVacuumPreResetCurvatureReserve.income G T D≤f*A:=
    (issued m).trans (WilsonVacuumPreResetCurvatureCharge.logarithm eta
      (zero_lt_one.trans (V.fits.delayed m)) gp band)
  have sc:=WilsonVacuumPreResetCurvatureCharge.physical gp one ab B.threshold_pos B.threshold_le
    (show B.threshold≤2*g*A by rw [ht];exact theta) mp tail alpha
  have bill:=WilsonVacuumPreResetCurvatureTariff.priced (G:=G) T D B ho hp hs γ β
  have mult:0≤|γ| *B.threshold^2+|β| *B.threshold^3+|β| *B.threshold^4:=by have := B.threshold_pos;positivity
  have fa:0≤f*A:=mul_nonneg fp (zero_le_one.trans ab)
  have spent:=bill.trans (mul_le_mul ip sc mult fa)
  have same:f*A*(20*(M+1)*g^3*A^4)=C*g^(11/4:ℝ):=by
    rw [←WilsonVacuumPreResetCurvatureCharge.gain gp]
    dsimp only [C,A,η];ring
  exact spent.trans (same ▸ clock N per (by omega))

end YM.Integration.WilsonVacuumPreResetSameCurvature
