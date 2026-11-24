import YM.Integration.WilsonIndependentSpoutHaarGerms

/-! Changing the normalized local Haar chart preserves the full actual action, measured clock, and every deposited ordinary field. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutHaarHistory
open Function Filter PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Soil PertExtension Metric Precision Exterior
open scoped Classical
variable {G:Gauge}{U V:ChartRatio G}(first:LocalRatio U)(second:LocalRatio V)(A:Levels G)
include first second

theorem lower (N m:ℕ)(X:Crude G):unripe A U N m X=unripe A V N m X:=by
  unfold unripe winter summer xray casePW plugζ
  simp only [WilsonIndependentSpoutHaarGerms.finite first second,WilsonIndependentSpoutHaarGerms.zeta first second]

theorem action (N m:ℕ)(X:Canvas G):season A U N m X=season A V N m X:=by
  unfold season tinge snow spurs stellar perζ
  simp only [WilsonIndependentSpoutHaarGerms.bearing first second,
    WilsonIndependentSpoutHaarGerms.zeta first second]

theorem step (N m:ℕ)(T:Mantle G):twinkle A U N m T=twinkle A V N m T:=by
  simp only [twinkle,lower first second,action first second]

theorem history (N m:ℕ):story A U N m=story A V N m:=by
  by_cases fine:m<N
  · rw [story_stride A U fine,story_stride A V fine,history N (m+1),step first second]
  · rw [story,dif_neg fine,story,dif_neg fine]
termination_by N-m

theorem pitch (N m:ℕ):Bank.pitch A U N m=Bank.pitch A V N m:=by
  simp only [Bank.pitch,freshet,actionW,history first second,action first second]

theorem reset (N m:ℕ):ratioHigh A U N m=ratioHigh A V N m:=by
  rw [ratioHigh,ratioHigh,pitch first second]

theorem clock (N m k:ℕ):relativeC A U N m k=relativeC A V N m k:=by
  simp only [relativeC,pitch first second]

variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
theorem marked (m N k:ℕ)(X:Era G E):verseI A U m N k X=verseI A V m N k X:=by
  unfold verseI reed srShade xray casePW windsT puck spurs stellar actionW
  simp only [history first second,reset first second,
    WilsonIndependentSpoutHaarGerms.finite first second,WilsonIndependentSpoutHaarGerms.bearing first second]

theorem original (N k c m:ℕ)(X:Era G E):cruises A U N k c m X=cruises A V N k c m X:=by
  by_cases early:m<c
  · rw [cruises_sub A U N k X early,cruises_sub A V N k X early,original N k c (m+1) X,marked first second]
  · rw [cruises,dif_neg early,cruises,dif_neg early]
termination_by c-m

end YM.Integration.WilsonIndependentSpoutHaarHistory
