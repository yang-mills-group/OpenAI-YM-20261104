import YM.Integration.WilsonReportingAbsoluteInletForecastMarket
import YM.Integration.WilsonReportingAbsoluteInletForecastSkyline
import YM.Integration.WilsonReportingAbsoluteInletForecastBookIncome
import YM.Integration.WilsonConditionalTaylorCourseAttachment

/-! Attach the same independently realized kinetic course to both filed
thermal Taylor series of the submitted forest and normalization choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastCanonical
open Filter Finset Real PowerSeries Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Series FormalBulk08.Wine MSbar MSbar.Cacao MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorCourseAttachment WilsonReportingAbsoluteInletForecastMarket
open WilsonReportingAbsoluteInletForecastBooks WilsonReportingAbsoluteInletForecastBookStep
open WilsonReportingAbsoluteInletForecastReciprocal WilsonReportingAbsoluteInletNativeDates WilsonReportingAbsoluteInletNativeInvoice
open scoped Classical Topology BigOperators
variable {G:Gauge}
variable (R:Run G) (simple:G.Simple)(u:G.ColorIndex)(V:MSbar.Heath.Voice G)(money:Terms u V R.kit)
variable (wood:∀j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags:∀j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include simple money in
theorem course (n:ℕ):
    Forward R n (fun N per j=>value n (bookU (price R u wood tags N per j)) (regulatorRun R.family N per j)) ∧
    Cost R n (price R u wood tags):=by
  obtain ⟨reports,load,hats,width,hoard⟩:=money
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2
    intro h
    filter_upwards [eventually_ge_atTop (R.t h)] with j hj
    exact (Nat.le_succ h).trans (((R.makes.stages h).2 j hj).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have fortune:=townsR R.b R.Q R.T R.t R.stories R.doors ch
  have rates:=Alto.skyline R.alloy.B n simple reports fortune 6 u (by decide)
  have visit:=sceneP R.b R.Q R.T R.t R.stories R.doors ch V (n+4) simple hoard u n 6 reports
    load hats width growth (by omega) (by decide) (by omega)
  obtain ⟨B,d,B0,priceCap⟩:=WilsonReportingAbsoluteInletForecastSkyline.prices n Alto.Dean
  obtain ⟨i,thermal⟩:=eventually_atTop.mp ((Alto.hats R.alloy.B simple).eventually_ge_atTop 1)
  let D:=price R u wood tags
  have issued:∀ᶠ k:ℕ in atTop,∀N per j,k ≤ j→j<N→
      (let g:=fun v=>regulatorRun R.family N per v
       |g j/g (j+1)-value n (bookU (D N per j)) (g j)| ≤
         (R.family.path.levels.clock.hatBeta j)^WilsonReportingAbsoluteInletForecastRate.exponent n) ∧
      mass n (bookU (D N per j))+mass n (bookH (D N per j)) ≤ B*(lag R.family j)^(2*d):=by
    filter_upwards [rates,visit,eventually_ge_atTop i] with k limits docket ik N per j kj jn
    obtain ⟨T,law⟩:=Alto.chosen R.alloy.B simple reports fortune N u n per (kj.trans jn.le)
    have paid (v:ℕ):Alto.Sampled (R.family.side v per) (R.family.path.levels.params v):=reports.pulse v per
    have field:=sceneField R simple u wood tags law (fun v _=>paid v) (j+1) jn (by omega)
    have aligned:=((nextField R simple u wood tags law j kj jn (paid j) field).2).1
    have valEq:value n (bookU (D N per j)) (regulatorRun R.family N per j)=
        MSbar.Bakery.taste n (T.action j) (regulatorRun R.family N per j):=by
      unfold WilsonReportingAbsoluteInletForecastBooks.value MSbar.Bakery.taste
      apply Finset.sum_congr rfl
      intro v hv
      rw [←aligned v (by have:=mem_range.mp hv;omega)]
    have original:=((docket N per T law).2 j kj jn)
    refine ⟨by dsimp only;rw [valEq];exact original,?_⟩
    let t:=Alto.hat R.family.path.levels j
    have t1:1 ≤ t:=thermal j (ik.trans kj)
    have priced:=priceCap (D N per j) t t1 (fun e he=>by
      rw [←aligned e he]
      exact (limits N per T law).2 j kj jn e he)
    have lt0:0 ≤ log (R.family.path.levels.clock.hatBeta j):=log_nonneg (R.family.path.levels.fits.delayed _).le
    have degree:t ≤ (lag R.family j)^2:=by change (Real.log _)^2 ≤ (2+Real.log _)^2;nlinarith only [lt0]
    have norm:t^d ≤ (lag R.family j)^(2*d):=by
      rw [pow_mul]
      exact pow_le_pow_left₀ (zero_le_one.trans t1) degree d
    exact priced.trans (mul_le_mul_of_nonneg_left norm B0)
  refine ⟨issued.mono (fun k h N per j kj jn=>(h N per j kj jn).1),B,2*d,B0,?_⟩
  exact issued.mono (fun k h N per j kj jn=>(h N per j kj jn).2)

include simple money in
theorem original (p:ℕ):InversePrice R p (fun N per j=>value (p+2) (bookH (price R u wood tags N per j))
    (regulatorRun R.family N per j)):=by
  obtain ⟨forward,cap⟩:=course R simple u V money wood tags (p+2)
  exact WilsonReportingAbsoluteInletForecastBookIncome.inverse R simple p _ money.2.2.1 forward cap
end YM.Integration.WilsonReportingAbsoluteInletForecastCanonical
