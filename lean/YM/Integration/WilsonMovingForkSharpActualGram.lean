import YM.Integration.WilsonMovingForkSharpUniform
import YM.Integration.WilsonMovingForkSharpAxisIntegral

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpActualGram
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
open WilsonMovingForkSharpUniform (Earned)

def Priced (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1)→SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(C₀ C₁ C₂ ledger:Credit)(u' z:ℕ)(φ:Rarity D)(ψ χ:Rarity Q.D)
    (S:𝓢(Euclid,ℂ))(x:Verse F)(M:ℝ):Prop:=
  ∀(older:ℕ),Y.vesselsC.anchor ≤ older → older ≤ Y.m → ∀(Z:Q.Rider)(y gap r:ℝ)(o:CellR),
    ClearDay φ χ gap → 0<gap → φ.radius+|y|+1 ≤ r → χ.radius+|y|+1 ≤ r →
    ∀(w:Fin 0→YForest G)(q:ℕ),q ≤ e →
    let top:=tested Y Q φ χ Z y o m older q x w S true
    let axisFare:=fare Y Q Z ledger m older q u' z r gap x
    let remainder:=((paceT Y.ax.S Y.m Y.ceilC)^h*gain Y)*|bill Y Q C₀ C₁ C₂ φ χ Z y gap r older|
    Integrable top ∧ ‖chamber Y m arms α X Q φ ψ Z older y o q w-∫ξ:Euclid,top ξ‖ ≤ 
      (remainder+axisFare)*(M*∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)

theorem original (p:h<D)(T:SectionData F)(Q:SealR G)(e u' z:ℕ):
    let toll:=Q.h+h+(u'+z+2)
    ∃ledger:Credit,∀{a u:ℕ}{v:Rails h k (u+a) e}(Y:CutsP H T p v C C C C),
      SpringD Y.vesselsC (h+Q.h) u' toll C → Dormitory Y.vesselsC (h+Q.h) u' C →
      ∀(m:ℕ)(arms:Fin (n+1)→SealR G)(α:Wilt arms)(X:Herit arms)(ticket:PassportC H Y.vesselsC Q C C)
       (C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)(room:Q.h ≤ k)(span:Y.ceilC ≤ m)(cut:m ≤ Y.N)
       (x:Verse F)(issued:x=(paceT Y.ax.S m Y.ceilC)^h • steep Y.ax Y.tx T p Y.N Y.ceilC (m-Y.ceilC) Y.tileP)
       (φ:Rarity D)(ψ χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
       (S:𝓢(Euclid,ℂ))(_spectral:∀j:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^j)*‖S ξ‖))
       (_field:Landed Y m arms α X Q φ ψ χ S),
       Priced Y m arms α X Q C₀ C₁ C₂ ledger u' z φ ψ χ S x (salary φ χ hφ hχ):=by
  intro toll
  obtain ⟨ledger,bought⟩:=WilsonMovingForkSharpAxisIntegral.original (H:=H) (k:=k) p T Q e u' z
  refine ⟨ledger,?_⟩
  intro a u v Y spring dorm m arms α X ticket C₀ C₁ C₂ paid room span cut x issued φ ψ χ hφ hχ S spectral field
  have sharp:=WilsonMovingForkSharpUniform.original Y m arms α X Q ticket C₀ C₁ C₂ paid room span cut x issued φ ψ χ hφ hχ S spectral field
  intro older gate route Z y gap r o clear pos near far w q grade top axisFare remainder
  let P:=tested Y Q φ χ Z y o m older q x w S false
  let κ:=salary φ χ hφ hχ
  let σ:=∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖
  obtain ⟨base,first⟩:=sharp older gate route Z y gap r o clear pos near far w q grade
  change Integrable P at base
  change _ ≤ remainder*(κ*σ) at first
  obtain ⟨cross,second⟩:=bought Y spring dorm ticket m older gate route φ χ hφ hχ S spectral Z o y gap r pos
    clear near far x q grade w
  change Integrable (top-P) at cross
  have summit:Integrable top:=by
    rw [show top=(top-P)+P by abel]
    exact cross.add base
  change ‖∫ξ:Euclid,(top ξ-P ξ)‖  ≤  axisFare*κ*σ at second
  rw [integral_sub summit base,norm_sub_rev] at second
  have triangle (a b c:ℝ):‖a-c‖≤‖a-b‖+‖b-c‖:=by
    rw [show a-c=(a-b)+(b-c) by ring]
    exact norm_add_le .. 
  refine ⟨summit,(triangle _ (∫ξ:Euclid,P ξ) _).trans ?_⟩
  apply (add_le_add first second).trans_eq
  ring
end YM.Integration.WilsonMovingForkSharpActualGram
