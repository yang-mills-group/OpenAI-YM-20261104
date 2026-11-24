import YM.Integration.WilsonMovingForkSharpBudget
import YM.Integration.WilsonSeparatedPrefixMovingBeforeRead

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGrades
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
open WilsonMovingForkSharpBudget (allowance Earned)
open WilsonIndependentMovingRosterAllFineRead (Heard)
def row (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1) → SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(φ:Rarity D)(ψ χ:Rarity Q.D)(S:𝓢(Euclid,ℂ))(x:Verse F)(Z:Q.Rider)
    (older:ℕ)(y:ℝ)(o:CellR)(w:Fin 0 → YForest G)(q:ℕ):ℝ:=
  chamber Y m arms α X Q φ ψ Z older y o q w-
    ∫ξ:Euclid,tested Y Q φ χ Z y o m older q x w S true ξ

def invoice (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂ ledger pay thermal:Credit)(u':ℕ)
    (φ:Rarity D)(χ:Rarity Q.D)(S:𝓢(Euclid,ℂ))(W:ℝ)(Z:Q.Rider)(older:ℕ)(y gap r:ℝ):ℝ:=
  (|bill Y Q C₀ C₁ C₂ φ χ Z y gap r older|+allowance Y Q Z ledger pay thermal older u' r gap)*
    (W*∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)

def Audited (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1) → SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(C₀ C₁ C₂ ledger pay thermal:Credit)(u':ℕ)(φ:Rarity D)(ψ χ:Rarity Q.D)
    (S:𝓢(Euclid,ℂ))(x:Verse F)(W:ℝ):Prop:=
  ∀(older:ℕ),Y.vesselsC.anchor ≤ older → older ≤ Y.m → ∀(Z:Q.Rider)(y gap r:ℝ)(o:CellR),
  ClearDay φ χ gap  →  0<gap  →  φ.radius+|y|+1 ≤ r  →  χ.radius+|y|+1 ≤ r  →  ∀w:Fin 0 → YForest G,
  let T':=paceT Y.ax.S m Y.m
  let size:=paceT Y.ax.S m Y.ceilC
  let gross:=invoice Y Q C₀ C₁ C₂ ledger pay thermal u' φ χ S W Z older y gap r
  let f:=row Y m arms α X Q φ ψ χ S x Z older y o w
  (∀q ≤ e,‖f q‖  ≤  T'^(-((h:ℝ)+1/4))*(size^((h:ℝ)+1/4)*gross)) ∧ Heard e h T' (size^h*gross) f

theorem original (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1) → SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(C₀ C₁ C₂ ledger pay thermal:Credit)(u':ℕ)(φ:Rarity D)(ψ χ:Rarity Q.D)
    (S:𝓢(Euclid,ℂ))(x:Verse F)(W:ℝ)(earned:Earned Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' φ ψ χ S x W):
    Audited Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' φ ψ χ S x W:=by
  intro older gate age Z y gap r o clear pos nr fr w T' size gross f
  let ρ:=paceT Y.ax.S Y.m Y.ceilC
  have paid (q:ℕ)(hq:q ≤ e):‖f q‖  ≤  (T'^(-((h:ℝ)+1/4))*size^((h:ℝ)+1/4))*gross:=
    (earned older gate age Z y gap r o clear pos nr fr w q hq).2
  have exactSize:=WilsonMovingForkSharpRuler.capture Y m
  change ρ^h*gain Y=T'^(-((h:ℝ)+1/4))*size^((h:ℝ)+1/4) at exactSize
  have source:0<ρ^h*gain Y:=mul_pos (pow_pos (pace_pos ..) _) (trail_pos ..)
  have amount:0 ≤ gross:=nonneg_of_mul_nonneg_right ((norm_nonneg _).trans
    (paid 0 (Nat.zero_le _))) (exactSize ▸ source)
  have native:gain Y ≤ 1:=WilsonMovingForkSharpRuler.unit Y
  constructor
  · intro q hq
    exact (paid q hq).trans_eq (mul_assoc ..)
  · apply WilsonSeparatedPrefixMovingBeforeRead.heard _ _ _ _ _ (pace_pos ..)
    intro q hq
    have strong:=paid q hq
    rw [←exactSize] at strong
    calc _ ≤ _:=strong
         _ ≤ ρ^h*gross:=mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left native (pow_nonneg (pace_pos ..).le h)).trans_eq (mul_one _)) amount
         _=_:=by rw [show ρ^h=(T'^h)⁻¹*size^h from WilsonMovingForkSharpRuler.ordinary Y m];ring
end YM.Integration.WilsonMovingForkSharpGrades
