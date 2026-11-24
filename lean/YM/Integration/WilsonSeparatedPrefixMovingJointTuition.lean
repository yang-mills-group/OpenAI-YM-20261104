import YM.Integration.WilsonSeparatedPrefixMovingJointRows

/-! Separate the exact filed input fees from the common optical and geometric prices. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointTuition
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named)
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{h D k n height seats:ℕ}{H:Hol G}{F:Labels.Frame G h}{T:SectionData F}{p:h<D}


open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open WilsonSeparatedPrefixMovingBookedMaster (Paid)
open scoped ContDiff
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingJointRows (bill)
def route (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)(φ:Rarity D)(χ:Rarity Q.D)
    (y gap r:ℝ)(older:ℕ):ℝ:=
  let Z:=epoch Y.vesselsC older Y.ceilC
  let radius:=max Z (max χ.radius |y|)
  let nearFee:=BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^(u+a)*C₀.buy Z)
  let farFee:=(hardCash e (u+a) C C C H Q).buy radius
  C₁.buy Z*(coinMat (k+Q.h) e*nearFee*farFee)+
    Z*((16*r)^u*(gap⁻¹)^a*((5*r)^4*9^(u+a))*((5*r)^4*9^(u+a))*C₂.buy Z)
theorem original (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)(φ:Rarity D)(χ:Rarity Q.D)
    (X:Q.Rider)(y gap r:ℝ)(older:ℕ):
    bill Y Q C₀ C₁ C₂ φ χ X y gap r older =
      route Y Q C₀ C₁ C₂ φ χ y gap r older*(Y.fuel*fee Q e X):=by
  dsimp only [bill,route,coupon];ring
end YM.Integration.WilsonSeparatedPrefixMovingJointTuition
