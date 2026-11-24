import YM.Integration.WilsonMovingForkSharpActualGram
import YM.Integration.WilsonMovingForkSharpCoordinate
import YM.Integration.WilsonMovingForkSharpRuler

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpBudget
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
open WilsonMovingForkSharpAxisCash (mass)
open WilsonMovingForkSharpReportClock (atFar)
open WilsonOlderFreshSoftCoverScalar (clock)
def allowance (Y:CutsP H T p v C C C C)(Q:SealR G)(X:Q.Rider)(ledger pay thermal:Credit)
    (older u':ℕ)(r gap:ℝ):ℝ:=
  let Z:=epoch Y.vesselsC older Y.ceilC
  2* |WilsonMovingForkSharpAxisWindow.wage (h:=h) Q X e u' (h+1) r gap 1 1| * |ledger.buy Z| * 
   ((Fintype.card (Alma F):ℝ)*(e+1:ℕ)*(thermal.buy Z*(pay.buy Z*Y.fuel)))

lemma quarter (Y:CutsP H T p v C C C C):
    paceT Y.ax.S Y.m Y.ceilC ≤ gain Y:=by
  rw [WilsonMovingForkSharpIncome.represented]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (pace_pos Y.ax.S Y.m Y.ceilC)
    (pace_le _ (Nat.le_add_right Y.m Y.i)) (show (4:ℝ)⁻¹ ≤ 1 by norm_num)

def Earned (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1)→SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(C₀ C₁ C₂ ledger pay thermal:Credit)(u':ℕ)(φ:Rarity D)(ψ χ:Rarity Q.D)
    (S:𝓢(Euclid,ℂ))(x:Verse F)(profilePay:ℝ):Prop:=
∀(older:ℕ),Y.vesselsC.anchor ≤ older → older ≤ Y.m → ∀(Z:Q.Rider)(y gap r:ℝ)(o:CellR),
      ClearDay φ χ gap → 0<gap → φ.radius+|y|+1 ≤ r → χ.radius+|y|+1 ≤ r → ∀(w:Fin 0→YForest G)(q:ℕ),q ≤ e →
      let M:=tested Y Q φ χ Z y o m older q x w S true
      let near:=|bill Y Q C₀ C₁ C₂ φ χ Z y gap r older|
      let cohorts:=allowance Y Q Z ledger pay thermal older u' r gap
      let T':=paceT Y.ax.S m Y.m
      let δ:=paceT Y.ax.S m Y.ceilC
      Integrable M ∧ ‖chamber Y m arms α X Q φ ψ Z older y o q w-∫ξ:Euclid,M ξ‖ ≤ 
        (T'^(-((h:ℝ)+1/4))*δ^((h:ℝ)+1/4))*((near+cohorts)*(profilePay*
          ∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖))

theorem original (p:h<D)(T:SectionData F)(Q:SealR G)(v:Rails h k (u+a) e)(u':ℕ):
    ∃ledger pay thermal:Credit,∀(Y:CutsP H T p v C C C C),
      SpringD Y.vesselsC (h+Q.h) u' (Q.h+h+(u'+(h+1)+2)) C → Dormitory Y.vesselsC (h+Q.h) u' C →
      ∀(m:ℕ)(arms:Fin (n+1)→SealR G)(α:Wilt arms)(X:Herit arms)(ticket:PassportC H Y.vesselsC Q C C)
       (C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)(room:Q.h ≤ k)(span:Y.ceilC ≤ m)(cut:m ≤ Y.N)
       (x:Verse F)(issued:x=(paceT Y.ax.S m Y.ceilC)^h • steep Y.ax Y.tx T p Y.N Y.ceilC (m-Y.ceilC) Y.tileP)
       (φ:Rarity D)(ψ χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
       (S:𝓢(Euclid,ℂ))(_spectral:∀j:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^j)*‖S ξ‖))
       (_field:Landed Y m arms α X Q φ ψ χ S),
      Earned Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' φ ψ χ S x (salary φ χ hφ hχ):=by
  obtain ⟨ledger,purchased⟩:=WilsonMovingForkSharpActualGram.original (H:=H) (k:=k) (n:=n) p T Q e u' (h+1)
  obtain ⟨pay,thermal,coordinates⟩:=WilsonMovingForkSharpCoordinate.original (H:=H) p T v
  refine ⟨ledger,pay,thermal,?_⟩
  intro Y spring dorm m arms α X ticket C₀ C₁ C₂ paid room span cut x issued φ ψ χ hφ hχ S spectral field
    older live age Z y gap r o clear pos nr fr w q grade M near cohorts T' δ
  obtain ⟨int,small⟩:=purchased Y spring dorm m arms α X ticket C₀ C₁ C₂ paid room span cut x issued
    φ ψ χ hφ hχ S spectral field older live age Z y gap r o clear pos nr fr w q grade
  have cap:=coordinates Y m older live age span cut x issued q grade
  let ρ:=paceT Y.ax.S Y.m Y.ceilC
  have pos':0<ρ:=pace_pos ..
  let weight:=salary φ χ hφ hχ*(∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)
  let room':=epoch Y.vesselsC older Y.ceilC
  let original:=mass (fun j=>clock Y.ax Y.tx Y.N Y.m older (atFar Y m x j)) q
  have dose:0 ≤ original:=by dsimp [original,mass];positivity
  have warm:1 ≤ room':=(window Y.vesselsC older older Y.ceilC live le_rfl (age.trans (Nat.le_add_right _ _))).1
  have ca:0 ≤ thermal.buy room'*(pay.buy room'*Y.fuel):=mul_nonneg (zero_le_one.trans (thermal.purchase warm))
    (mul_nonneg (zero_le_one.trans (pay.purchase warm)) Y.hf)
  have massBound:original ≤ (Fintype.card (Alma F):ℝ)*(e+1:ℕ)*(thermal.buy room'*(pay.buy room'*Y.fuel)):=by
    apply cap.trans
    gcongr
  have decay:ρ^(h+1) ≤ ρ^h*gain Y:=by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (quarter Y) (pow_nonneg pos'.le _)
  have factor:fare Y Q Z ledger m older q u' (h+1) r gap x ≤ (ρ^h*gain Y)*cohorts:=by
    unfold fare
    change |original*(2*(WilsonMovingForkSharpAxisWindow.wage (h:=h) Q Z e u' (h+1) r gap 1 1*ρ^(h+1))*ledger.buy room')| ≤ _
    rw [abs_mul,abs_of_nonneg dose,abs_mul,abs_mul,abs_mul,abs_of_nonneg (pow_nonneg pos'.le _)]
    have eq:|2|=(2:ℝ):=abs_of_pos (by norm_num)
    rw [eq]
    have strength:0 ≤ gain Y:=(trail_pos ..).le
    dsimp only [cohorts,allowance]
    calc _=ρ^(h+1)*(2* |WilsonMovingForkSharpAxisWindow.wage (h:=h) Q Z e u' (h+1) r gap 1 1| * |ledger.buy room'|)*original:=by ring
         _ ≤ _:=(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right decay (by positivity)) dose).trans
           ((mul_le_mul_of_nonneg_left massBound (by positivity)).trans_eq (by ring))
  have ww:0 ≤ weight:=mul_nonneg (WilsonSeparatedPrefixMovingSpectralSalary.positive φ χ hφ hχ)
    (integral_nonneg fun ξ=>mul_nonneg (by positivity) (norm_nonneg _))
  have rr:=WilsonMovingForkSharpRuler.capture Y m
  change ρ^h*gain Y=T'^(-((h:ℝ)+1/4))*δ^((h:ℝ)+1/4) at rr
  refine ⟨int,?_⟩
  rw [←rr]
  apply small.trans
  calc _ ≤ (ρ^h*gain Y*near+(ρ^h*gain Y)*cohorts)*weight:=mul_le_mul_of_nonneg_right
           (add_le_add_right factor _) ww
       _=_:=by ring
end YM.Integration.WilsonMovingForkSharpBudget
