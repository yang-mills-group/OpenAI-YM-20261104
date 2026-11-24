import YM.Integration.WilsonMovingForkSharpSalary

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpUniform
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
def Earned (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1)→SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(C₀ C₁ C₂:Credit)(φ:Rarity D)(ψ χ:Rarity Q.D)(S:𝓢(Euclid,ℂ))(x:Verse F)(M:ℝ):Prop:=
  ∀(older:ℕ),Y.vesselsC.anchor ≤ older → older ≤ Y.m → ∀(Z:Q.Rider)
    (y gap r:ℝ)(o:CellR),ClearDay φ χ gap → 0<gap →
    φ.radius+|y|+1 ≤ r → χ.radius+|y|+1 ≤ r → ∀(w:Fin 0→YForest G)(q:ℕ),q ≤ e →
      let axis:=projected Y Q φ χ Z y o m older q x w S
      let invoice:=bill Y Q C₀ C₁ C₂ φ χ Z y gap r older
      Integrable axis ∧ ‖chamber Y m arms α X Q φ ψ Z older y o q w - ∫ξ:Euclid,axis ξ‖
        ≤ ((paceT Y.ax.S Y.m Y.ceilC)^h * gain Y)*(abs invoice)*(M*(∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖))

theorem original (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1)→SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(ticket:PassportC H Y.vesselsC Q C C)(C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)
    (room:Q.h ≤ k)(formed:Y.ceilC ≤ m)(cut:m ≤ Y.N)(x:Verse F)
    (issued:x=(paceT Y.ax.S m Y.ceilC)^h • steep Y.ax Y.tx T p Y.N Y.ceilC (m-Y.ceilC) Y.tileP)
    (φ:Rarity D)(ψ χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (S:𝓢(Euclid,ℂ))(spectral:∀j:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^j)*‖S ξ‖))
    (field:Landed Y m arms α X Q φ ψ χ S):Earned Y m arms α X Q C₀ C₁ C₂ φ ψ χ S x (salary φ χ hφ hχ):=by
  have estimate:=WilsonMovingForkSharpSalary.received Y Q ticket C₀ C₁ C₂ paid φ χ hφ hχ S spectral
  intro older gate age Z y gap r o clear positive near far w q grade axis invoice
  let incoming:=full Y Q φ χ Z y o older q w S
  let residual:=signedRow Y Q φ χ Z y o older q w S
  obtain ⟨good,raw⟩:=field Z older (age.trans (Nat.le_add_right ..)) y o q 0 w
  change Integrable incoming at good
  change chamber Y m arms α X Q φ ψ Z older y o q w=∫ξ:Euclid,incoming ξ at raw
  obtain ⟨stable,small⟩:=estimate older gate age Z y gap r o clear positive near far w q grade
  have difference:incoming-axis=residual:=funext (WilsonMovingForkSharpProfile.pointwise Y Q ticket room m formed cut x issued
    φ χ Z y o older age q w S)
  have axes:Integrable axis:=by
    have equal:axis=incoming-residual:=by rw [←difference];abel
    rw [equal]
    exact good.sub stable
  refine ⟨axes,?_⟩
  rw [raw,←integral_sub good axes]
  change ‖∫ξ:Euclid,(incoming-axis) ξ‖ ≤ _
  rw [difference]
  exact small

end YM.Integration.WilsonMovingForkSharpUniform
