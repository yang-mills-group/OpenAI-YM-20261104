import YM.Integration.WilsonSeparatedPrefixMovingPinnedRaw
import YM.Integration.WilsonMovingForkSharpRetainedBook

/-! True upper product against the complete all-cutoff reflected coefficient rows on a single elected Mer board. -/
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinnedContrast
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

open MeasureTheory
open scoped SchwartzMap ContDiff
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointExpansion (coefficient angle)
open WilsonSeparatedPrefixMovingJointIntegral (signedRow)
open WilsonSeparatedPrefixMovingJointRows (bill)
open WilsonSeparatedPrefixMovingJointAddress (move)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonMovingForkSharpMaster (Paid)
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingRelativeMaster (Landed)
open WilsonMovingForkSharpProfile (full projected)
open WilsonMovingForkSharpIncome (gain)
open WilsonMovingForkSharpIntegral (chamber)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
open WilsonMovingForkSharpAxisIntegral (fare)
open WilsonMovingForkSharpAxisWave (tested)

open WilsonMovingForkSharpActualGram (Priced)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingPinChamber (panel)
open WilsonSeparatedPrefixMovingPinnedRaw (raw)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonMovingForkSharpBudget (allowance)
open WilsonMovingForkSharpAxisCash (mass)
open WilsonMovingForkSharpReportClock (atFar)
open WilsonOlderFreshSoftCoverScalar (clock)

theorem original (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1)→SealR G)(Q:SealR G)(α:Wilt arms)(X:Herit arms)
    (C₀ C₁ C₂ ledger pay thermal:Credit)(u':ℕ)(Φ:Rarity D)(ψ χ:Rarity Q.D)(S:𝓢(Euclid,ℂ))(x:Verse F)(profilePay:ℝ)
    (issued:WilsonMovingForkSharpBudget.Earned Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' Φ ψ χ S x profilePay)
    (owners:HorizonP H Y.vesselsC C C arms)(far:PassportC H Y.vesselsC Q C C)(Z:Q.Rider)(older h₀:ℕ)
    (live:Y.vesselsC.anchor≤older)(ear:older≤Y.m)(top:Y.ceilC≤Y.N)(y gap r price:ℝ)(o:CellR)
    (apart:ClearDay Φ χ gap)(positive:0<gap)(inner:Φ.radius+|y|+1≤r)(external:χ.radius+|y|+1≤r)(w:Fin 0→YForest G)
    (before:Heard e h₀ (paceT Y.ax.S m Y.m) price (fun q=>
      panel Y.vesselsC arms Q α ψ X Z Φ y o Y.m m Y.ceilC older Y.N Y.N q 0 w-
      panel Y.vesselsC arms Q α ψ X Z Φ y o Y.m m Y.ceilC older Y.N Y.ceilC q 0 w)):
    let T':=paceT Y.ax.S m Y.m
    let δ:=paceT Y.ax.S m Y.ceilC
    let near:=|bill Y Q C₀ C₁ C₂ Φ χ Z y gap r older|
    let cohorts:=allowance Y Q Z ledger pay thermal older u' r gap
    let joint:=profilePay*(∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)
    let rough:=(T'^h₀)⁻¹*price
    let compensated:=(T'^(-((h:ℝ)+1/4))*δ^((h:ℝ)+1/4))*((near+cohorts)*joint)
    let rows:=fun q=>tested Y Q Φ χ Z y o m older q x w S true
    (∀q≤e,Integrable (rows q)) ∧ Heard e 0 T' (rough+compensated) (fun q=>
      raw Y.vesselsC arms Q α ψ X Z Φ y o Y.m m Y.ceilC older Y.N q 0 w-∫ξ:Euclid,rows q ξ):=by
  intro T' δ near cohorts joint rough compensated rows
  have bEar:older≤Y.ceilC:=ear.trans (Nat.le_add_right ..)
  have bLive:=live.trans bEar
  have after (q:ℕ)(hq:q≤e):=issued older live ear Z y gap r o apart positive inner external w q hq
  refine ⟨fun q hq=>(after q hq).1,?_⟩
  apply WilsonSeparatedPrefixMovingBeforeRead.heard _ _ _ _ _ (pace_pos ..)
  intro q hq
  rw [pow_zero,inv_one,one_mul]
  have entered:=WilsonSeparatedPrefixMovingPinnedRaw.original Y.vesselsC arms Q owners far α ψ X Z Φ y o
    Y.m m Y.ceilC older Y.N q 0 w (bLive.trans top) (bEar.trans top) top
  have captured:=WilsonSeparatedPrefixMovingPinChamber.captured Y.vesselsC arms Q owners far α ψ X Z Φ y o
    Y.m m Y.ceilC older Y.N h q 0 w bLive bEar top
  change panel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y.ceilC q 0 w=chamber Y m arms α X Q Φ ψ Z older y o q w at captured
  rw [←entered]
  calc
    _≤ ‖panel Y.vesselsC arms Q α ψ X Z Φ y o Y.m m Y.ceilC older Y.N Y.N q 0 w-chamber Y m arms α X Q Φ ψ Z older y o q w‖+
      ‖chamber Y m arms α X Q Φ ψ Z older y o q w-∫ξ:Euclid,rows q ξ‖:=norm_sub_le_norm_sub_add_norm_sub .. 
    _≤ _:=add_le_add (captured ▸ before.1 q hq) (after q hq).2
end YM.Integration.WilsonSeparatedPrefixMovingPinnedContrast
