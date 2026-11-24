import YM.Integration.WilsonSeparatedPrefixMovingInvoice
import YM.Integration.WilsonSeparatedPrefixMovingNearReturn
import YM.Integration.WilsonSeparatedPrefixMovingOwnDate

/-! A first join after capture. The near source includes the old scalar
and is the complete propagated difference on its own nominated chart.
The reflected exterior enters as its literal own-date normalized column. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCapturedFees
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

theorem age {v:Rails h k u e}(Y:CutsP H T p v E W K U)(older:ℕ)(live:Y.vesselsC.anchor ≤ older)
    (stop:older ≤ Y.m):Y.Age ≤ epoch Y.vesselsC older Y.ceilC:=by
  have bought:Compar Y.ax.S Y.vesselsC.y Y.m Y.ceilC ≤ epoch Y.vesselsC older Y.ceilC:=
    (window Y.vesselsC older Y.m Y.ceilC live stop (Nat.le_add_right _ _)).2.2.1
  simpa only [CutsP.Age,WindowS.Age,CutsP.windowC,CutsP.ceilC,CutsP.ax,Compar,Nat.add_sub_cancel_left]
    using bought

theorem income {v:Rails h k u e}(Y:CutsP H T p v E W K U)(C:Credit)(j:ℕ)(fund:j ≤ Y.i)
    (Z:ℝ)(licensed:Y.Age ≤ Z):
    Earned Z C (price Y C j 1) Y.fuel:=by
  let diff:=Y.ax.S.scale Y.ceilC-Y.ax.S.scale (Y.m+j)
  have cp:0 ≤ C.buy Y.Age:=zero_le_one.trans (C.purchase Y.windowC.warm)
  have own:0 ≤ diff:=sub_nonneg.mpr (scales Y.ax.S (Nat.add_le_add_left fund _))
  have expBound:Real.exp (-diff/4) ≤ 1:=Real.exp_le_one_iff.mpr (by linarith)
  have bill:0 ≤ C.buy Y.Age*Real.exp (-diff/4)*Y.fuel:=
    mul_nonneg (mul_nonneg cp (Real.exp_pos _).le) Y.hf
  refine ⟨?_,?_⟩
  · simpa only [WilsonIndependentMatchedCoverProfile.price,abs_one,one_mul,diff] using bill
  · have small: C.buy Y.Age*Real.exp (-diff/4) ≤ C.buy Z:=
      (mul_le_of_le_one_right cp expBound).trans (Credit.elder C Y.windowC.warm licensed)
    simpa only [WilsonIndependentMatchedCoverProfile.price,abs_one,one_mul,diff] using mul_le_mul_of_nonneg_right small Y.hf

theorem mount {v:Rails h k u e}(Y:CutsP H T p v E W K U)(C:Credit)(j:ℕ)(fund:j ≤ Y.i)
    (Z:ℝ)(licensed:Y.Age ≤ Z)(φ:Rarity D)(b:ℕ)(x y r B:ℝ)(cap:radiusH φ x y ≤ r)(invoice:Amplitude φ B):
    Earned Z C ((5*radiusH φ x y)^4*(9^b*(B*price Y C j 1)))
      ((5*r)^4*(9^b*(B*Y.fuel))):=by
  have got:=income Y C j fund Z licensed
  have radius:0 ≤ radiusH φ x y:=zero_le_one.trans (fieldCap ..)
  have cn:0 ≤ C.buy Z:=zero_le_one.trans (C.purchase (Y.windowC.warm.trans licensed))
  have bb:=invoice.1
  refine ⟨by have n:=got.floor;positivity,?_⟩
  calc
    _ ≤ (5*r)^4*(9^b*(B*(C.buy Z*Y.fuel))):=by
      have nonneg:=got.floor
      have invoicePaid:=got.grant
      gcongr
    _=_:=by ring

end YM.Integration.WilsonSeparatedPrefixMovingCapturedFees
