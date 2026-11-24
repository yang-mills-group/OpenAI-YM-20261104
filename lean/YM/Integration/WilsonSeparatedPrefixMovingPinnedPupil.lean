import YM.Integration.WilsonSeparatedPrefixMovingPinnedContrast
import YM.Integration.WilsonSeparatedPrefixMovingPinnedMaster

/-! Buy the full raw-to-reported reflected moment and its strict perturbative tail on the same causal programme. -/
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinnedPupil
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

open WilsonIndependentMovingRosterAllFineSeats (needed)
open WilsonIndependentMovingRosterBirthCalendar (room)

def frontPrice (R:Realm G (e+1) C)(arms:Fin (n+1) → SealR G)(Q:SealR G)(X:Herit arms)(Z:Q.Rider)
    (first shape chron middle:Credit)(target older _t b m:ℕ)(r nearGap farGap DF:ℝ)(B:Fin (n+1) → ℝ):ℝ:=
  let y:=paceT R.draws.S m b
  let k:=Q.h+capP arms
  let τ:=target+k
  let a:=Q.h+(0+τ)
  let anew:=capP arms+Q.h+(0+τ+2)
  let amid:=Q.h+(0+τ+2)
  let age:=epoch R older m
  let fresh:=WilsonSeparatedPrefixMovingUnformedSector.invoice arms Q X Z e k 0 anew r farGap DF B
  let old:=shape.buy (room r nearGap y)*WilsonIndependentMovingRosterInvoice.charge arms Q X Z e 0 a r farGap DF B
  let stable:=(16*r)^0*(farGap⁻¹)^amid*coupon Q Z e (0+amid) r DF*9^(0+amid)*(∏s,B s*fee (arms s) e (X s))
  2*fresh*first.buy age+4*old*chron.buy age+y^target*(age*(stable*middle.buy age))

def Clear (R:Realm G (e+1) C)(arms:Fin (n+1) → SealR G)(Q:SealR G)(α:Wilt arms)(ψ:Rarity Q.D)
    (older t b m:ℕ)(r nearGap farGap DF:ℝ)(B:Fin (n+1) → ℝ):Prop:=
  let y:=paceT R.draws.S m b
  let T':=paceT R.draws.S m t
  0<nearGap ∧ 0<farGap ∧ (∀s,Amplitude (α s) (B s))∧Amplitude ψ DF ∧
    (∀s d,s≠d → ClearDay (α s) (α d) nearGap)∧(∀s,(α s).radius+|y|+1 ≤ r)∧
    ψ.radius+|y/T'|+1 ≤ r ∧ 2+2*|y| ≤ r ∧ room r nearGap y ≤ epoch R older m ∧
    ∀z∈tsupport ψ.ψ.val,T'*farGap+max r (y+|y|) ≤ ‖T' • z‖

theorem original (M:Master H)(p:h<D)(T:SectionData F)(arms:Fin (n+1) → SealR G)(Q:SealR G)
    (v:Rails h k (u+a) e)(u' target:ℕ)(ht:0<target)
    (near:∀s,Named M height seats (arms s))(far:Named M height seats Q)
    (rankNear:capP arms ≤ k)(rankFar:Q.h ≤ k)(budget:needed (Q.h+capP arms) 0 target ≤ seats)
    (pairRoom:Q.h+h+(u'+(h+1)+2) ≤ seats):
    ∃first shape chron middle ledger pay thermal:Credit,∀(Y:CutsP H T p v C C C C)(_sold:Elected M Y.vesselsC height seats)
      (C₀ C₁ C₂:Credit)(_paid:Paid Y Q C₀ C₁ C₂)(m:ℕ)(α:Wilt arms)(X:Herit arms)(x:Verse F),
      Y.ceilC ≤ m → m ≤ Y.N → x=(paceT Y.ax.S m Y.ceilC)^h • steep Y.ax Y.tx T p Y.N Y.ceilC (m-Y.ceilC) Y.tileP → 
      Y.pt=AutumnDay Y.ax Y.tx α X m Y.ceilC Y.N D → 
    ∀(Φ:Rarity D)(ψ χ:Rarity Q.D)(hΦ:ContDiff ℝ ∞ Φ.ψ.val)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val),
      (∀p q:Point4,Φ.ψ.val p*ψ.ψ.val (q-p)=Φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))) → 
    ∀(older:ℕ),Y.vesselsC.anchor ≤ older →  older ≤ Y.m →  ∀(Z:Q.Rider)(r δ₀ δ₁ DF:ℝ)(B:Fin (n+1) → ℝ),
      Clear Y.vesselsC arms Q α ψ older Y.m Y.ceilC m r δ₀ δ₁ DF B → 
    ∀(y gap out A:ℝ)(o:CellR)(w:Fin 0 → YForest G),Amplitude Φ A → ClearDay Φ χ gap → 0<gap → Φ.radius+|y|+1 ≤ out → χ.radius+|y|+1 ≤ out → 
      let T':=paceT Y.ax.S m Y.m
      let δ:=paceT Y.ax.S m Y.ceilC
      let ε:=paceT Y.ax.S Y.m Y.ceilC
      let S:=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ
      let credited:=(5*radiusH Φ ε y)^4*A*frontPrice Y.vesselsC arms Q X Z first shape chron middle target older Y.m Y.ceilC m r δ₀ δ₁ DF B
      let near:=|bill Y Q C₀ C₁ C₂ Φ χ Z y gap out older|
      let cohorts:=allowance Y Q Z ledger pay thermal older u' out gap
      let joint:=salary Φ χ hΦ hχ*(∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)
      let rows:=fun q=>tested Y Q Φ χ Z y o m older q x w S true
      (∀q ≤ e,Integrable (rows q))∧Heard e 0 T'
        ((T'^target)⁻¹*credited+(T'^(-((h:ℝ)+1/4))*δ^((h:ℝ)+1/4))*((near+cohorts)*joint))
        (fun q=>raw Y.vesselsC arms Q α ψ X Z Φ y o Y.m m Y.ceilC older Y.N q 0 w-∫ξ:Euclid,rows q ξ):=by
  obtain ⟨first,shape,chron,middle,before⟩:=WilsonSeparatedPrefixMovingPinBefore.original M arms Q e target ht near far budget
  obtain ⟨ledger,pay,thermal,after⟩:=WilsonMovingForkSharpRetainedBook.original (H:=H) (n:=n) p T Q v u'
  refine ⟨first,shape,chron,middle,ledger,pay,thermal,?_⟩
  intro Y sold C₀ C₁ C₂ paid m α X x bf top report admitted Φ ψ χ hΦ hψ hχ collar older real ear Z r δ₀ δ₁ DF B cleared y gap out A o w much sep sepPos Φroom χroom T' δ ε S credited nearC cohorts joint rows
  obtain ⟨owners,⟨outside⟩⟩:=WilsonIndependentMovingRosterAllFineSeats.roster sold arms Q near far
  have senior:=sold.spring (h+Q.h) u' (Q.h+h+(u'+(h+1)+2)) (by omega) pairRoom (by omega)
  have closed:=sold.dorm (h+Q.h) u' (by omega) (by omega)
  have codes:=after Y senior closed m arms α X outside owners C₀ C₁ C₂ paid rankFar rankNear bf top x report admitted Φ ψ χ hΦ hψ hχ collar
  obtain ⟨nearPos,farPos,nearIncome,farIncome,apart,fits,farBox,nearBox,shield,remote⟩:=cleared
  have high:=WilsonSeparatedPrefixMovingPinChamber.original Y.vesselsC arms Q owners outside α ψ X Z Φ y o Y.m m Y.ceilC older Y.N target w
    (real.trans (ear.trans (Nat.le_add_right ..))) (ear.trans (Nat.le_add_right ..)) (bf.trans top)
    (pace_le _ (Nat.le_add_right ..)) A (frontPrice Y.vesselsC arms Q X Z first shape chron middle target older Y.m Y.ceilC m r δ₀ δ₁ DF B) much
      (fun z s=>before Y.vesselsC sold older Y.m Y.ceilC m Y.N real ear (Nat.le_add_right ..) bf top α ψ X Z z δ r δ₀ δ₁ DF B nearPos farPos nearIncome farIncome apart fits farBox nearBox shield remote s w)
  exact WilsonSeparatedPrefixMovingPinnedContrast.original Y m arms Q α X C₀ C₁ C₂ ledger pay thermal u' Φ ψ χ S x (salary Φ χ hΦ hχ) codes.2.2.1 owners outside Z older target real ear (bf.trans top) y gap out credited o sep sepPos Φroom χroom w high
end YM.Integration.WilsonSeparatedPrefixMovingPinnedPupil
