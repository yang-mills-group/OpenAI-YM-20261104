import YM.Integration.WilsonVacuumPreResetRenderQuote
import YM.Integration.WilsonVacuumPreResetRenderTime
import YM.Integration.WilsonLimitConstruction.FundedSpringPeriodRows

/-! One pre-period covering correction carries both its independently
rebooked finite formal series and its small original reset fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiledQuote
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
    (paths:FundedOriginalVacuumPaths.prices R.kit)(issued:WilsonVacuumPreResetRenderCalendar.Issued R.kit)
    (time:RG01Estimate.Chart.Barrier R.alloy (fun _ i=>((i:ℝ)+1)⁻¹))(e:ℕ){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∃W:Credit,∀ᶠm:ℕ in atTop,∃σ:ℝ,0<σ ∧ σ⁻¹≤zz V (m+1) ∧
      ∀N:ℕ,m+1<N→let C:=W.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∃Z:SeriesA G,(∀a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧ Z.length≤ meterPre (3+e) ∧
      Draw Z σ C ∧ RunFundedPeriodAction.PeriodData Z (2+e) σ C ∧
      (∀k<3+e,∀n:Side,∀l,Blue.mix (pace (pitch V R.metals.O N (m+1)))
        (front (R.alloy.B.kin.path N (m+1)) (V.params (m+1)).clip n+sands Z n) k (l+1)=
        lagoon (freshet V R.metals.O N (m+1) k (l+1)) n) ∧
      ∀per:ℕ,let g:=regulatorRun R.family N per (m+1)
        let p:=OriginalMarkedRunAction.finitePitch R N (m+1) (2+e) g
        ∀(n:Side)(B:BudgetPoint),B.order=(V.params m).order→B.power=(V.params m).power→
        B.supportExponent≤(V.params m).supportExponent+6→B.threshold=(V.budget m).threshold→
        |quote (Z.map (FundedCorrectedPeriod.piece n B σ C)) (weight g p)|≤ε*Time.forecastE V m:=by
  intro V
  obtain ⟨W,chosen⟩:=FundedSpringPeriodRows.funded R simple v rows paths e
  obtain ⟨_,heat⟩:=OriginalMarkedRunAction.cofinal_temperature R simple v rows (2+e)
  let cap:=3+e
  let K:ℝ:=meterPre cap*(12*2^(cap+2))
  refine ⟨W,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually chosen,(tendsto_add_atTop_nat 1).eventually heat,
    WilsonVacuumPreResetRenderQuote.original R issued simple W cap,
    WilsonVacuumPreResetRenderTime.original R simple time K (by dsimp [K];positivity) ep] with m filed thermal funds clock
  obtain ⟨σ,positive,width,source⟩:=filed
  refine ⟨σ,positive,width,?_⟩
  intro N hm C
  obtain ⟨Z,grade,before,size,draw,data,formal⟩:=source N hm
  refine ⟨Z,grade,before,size,draw,data,formal,?_⟩
  intro per g p n B order power exponent threshold
  obtain ⟨_,_,low,high,_,_⟩:=thermal N hm per
  have k:m<N:=by omega
  have paid:=funds N per k n B σ p Z positive width low (high.trans (by norm_num)) order power exponent threshold
    (fun a h=>⟨grade a h,(before a h).le⟩)
  have count:(Z.length:ℝ)≤ meterPre cap:=by exact_mod_cast size
  apply paid.trans
  apply le_trans _ (clock N per k)
  dsimp only [K]
  gcongr
  exact Real.rpow_nonneg (IterationFour.Currency.g_pos R.makes N per (m+1) hm.le).le _

end YM.Integration.WilsonVacuumPreResetFiledQuote
