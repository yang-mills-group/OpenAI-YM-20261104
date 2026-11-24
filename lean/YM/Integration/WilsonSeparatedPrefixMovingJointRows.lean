import YM.Integration.WilsonSeparatedPrefixMovingBookedMaster
import YM.Integration.WilsonSeparatedPrefixMovingJointExpansion

/-! Financial incidence of every real Fourier pair directly on the earlier enrolled Mer scalar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointRows
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
def bill (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)(φ:Rarity D)(χ:Rarity Q.D)
    (X:Q.Rider)(y gap r:ℝ)(older:ℕ):ℝ:=
  let Z:=epoch Y.vesselsC older Y.ceilC
  let Z₁:=max Z (max χ.radius |y|)
  let nearFee:=BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^(u+a)*(C₀.buy Z*Y.fuel))
  let farFee:=(hardCash e (u+a) C C C H Q).buy Z₁*WilsonSeparatedPrefixMovingOwnDate.fee Q e X
  let residue:=C₁.buy Z*(coinMat (k+Q.h) e*nearFee*farFee)
  let joins:=(16*r)^u*(gap⁻¹)^a*((5*r)^4*(9^(u+a)*Y.fuel))*coupon Q X e (u+a) r 1
  residue+Z*(joins*C₂.buy Z)
def page (Y:CutsP H T p v C C C C)(Q:SealR G)(φ:Rarity D)(χ:Rarity Q.D)(X:Q.Rider)(y:ℝ)
    (o:CellR)(older q:ℕ)(legs:Fin 0→YForest G)(ξ:Euclid)(c d:Bool):ℝ:=
  (whole Y Q (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X y o older Y.i).2 q 0 legs
private theorem support {l:ℕ}(φ:Rarity l)(ℓ:Point4→L[ℝ]ℝ)(c:Bool):
    tsupport (sheet φ ℓ c).ψ.val ⊆ tsupport φ.ψ.val:=by
  apply closure_mono
  intro x hx
  apply left_ne_zero_of_mul (b:=WilsonSeparatedPrefixMovingJointWaves.wave c (ℓ x))
  exact hx
theorem original (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val):
    ∃M:ℝ,0≤M ∧ ∀(older:ℕ)(_gate:Y.vesselsC.anchor≤older)(_route:older≤Y.m)(X:Q.Rider)
      (y gap r:ℝ)(o:CellR)(_clear:ClearDay φ χ gap)(_pos:0<gap)
      (_near:φ.radius+|y|+1≤r)(_far:χ.radius+|y|+1≤r)(legs:Fin 0→YForest G)(ξ:Euclid)(c d:Bool)
      (q:ℕ)(_grade:q≤e),
      ‖page Y Q φ χ X y o older q legs ξ c d‖≤(paceT Y.ax.S Y.m Y.ceilC)^h*
        bill Y Q C₀ C₁ C₂ φ χ X y gap r older*(M*(1+‖angle ξ‖)^(D+Q.D)):=by
  obtain ⟨A,hA,near⟩:=WilsonSeparatedPrefixMovingJointWaves.original φ hφ
  obtain ⟨B,hB,far⟩:=WilsonSeparatedPrefixMovingJointWaves.original χ hχ
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro older gate route X y gap r o clear pos nr fr legs ξ c d q grade
  have apart:ClearDay (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) gap:=
    fun x hx z hz=>clear x (support _ _ _ hx) z (support _ _ _ hz)
  have line:=(paid older gate route (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X y gap r
    (A*(1+‖angle ξ‖)^D) (B*(1+‖angle ξ‖)^Q.D) o (near _ _) (far _ _) apart pos nr fr legs).1 q grade
  apply line.trans_eq
  dsimp only [bill,BasePrice,radiusH,WilsonSeparatedPrefixMovingJointWaves.sheet,coupon]
  rw [pow_add]
  ring
end YM.Integration.WilsonSeparatedPrefixMovingJointRows
