import YM.Integration.WilsonMovingForkSharpIncome

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpRuler
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D a k k' e u extra:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {E W K U V V' L:Credit}

open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingInvoice (Earned)
open scoped Classical

/-- The genuine finite capture and the physical fine-to-far ratio on that same schedule. -/
theorem capture {v:Rails h k u e}(Y:CutsP H T p v E W K U)(m:ℕ):
    (paceT Y.ax.S Y.m Y.ceilC)^h*WilsonMovingForkSharpIncome.gain Y =
       (paceT Y.ax.S m Y.m)^(-((h:ℝ)+1/4))*(paceT Y.ax.S m Y.ceilC)^((h:ℝ)+1/4):=by
  have link : paceT Y.ax.S Y.m Y.ceilC = (paceT Y.ax.S m Y.ceilC)/(paceT Y.ax.S m Y.m):=by
    unfold paceT
    field_simp [(Y.ax.S.a_pos m).ne',(Y.ax.S.a_pos Y.m).ne']
  rw [WilsonMovingForkSharpIncome.represented,←Real.rpow_natCast _ h,
    ←Real.rpow_add (pace_pos ..),link,Real.div_rpow (pace_pos ..).le (pace_pos ..).le,
    Real.rpow_neg (pace_pos ..).le]
  simp only [div_eq_inv_mul,mul_one]

theorem ordinary {v:Rails h k u e}(Y:CutsP H T p v E W K U)(m:ℕ):
    (paceT Y.ax.S Y.m Y.ceilC)^h =
       ((paceT Y.ax.S m Y.m)^h)⁻¹*(paceT Y.ax.S m Y.ceilC)^h:=by
  have link : paceT Y.ax.S Y.m Y.ceilC = (paceT Y.ax.S m Y.ceilC)/(paceT Y.ax.S m Y.m):=by
    unfold paceT
    field_simp [(Y.ax.S.a_pos m).ne',(Y.ax.S.a_pos Y.m).ne']
  rw [link,div_pow,div_eq_inv_mul]

theorem unit {v:Rails h k u e}(Y:CutsP H T p v E W K U):WilsonMovingForkSharpIncome.gain Y≤1:=by
  unfold WilsonMovingForkSharpIncome.gain trailC
  apply Real.exp_le_one_iff.mpr
  have base:=scales Y.ax.S (Nat.le_add_right Y.m Y.i)
  change Y.ax.S.scale Y.m≤Y.ax.S.scale Y.ceilC at base
  linarith
end YM.Integration.WilsonMovingForkSharpRuler
