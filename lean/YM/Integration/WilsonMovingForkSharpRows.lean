import YM.Integration.WilsonMovingForkSharpMaster
import YM.Integration.WilsonMovingForkSharpProjected
import YM.Integration.WilsonMovingForkSharpRuler
import YM.Integration.WilsonIndependentMovingRosterAllFineSeats
import YM.Integration.WilsonSeparatedPrefixMovingMiddleIncome

/-! The actual signed full-minus-counterterm column with its own conditioned far
  field, at both the low spatial rate and the finite high-order rate. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpRows
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

open WilsonMovingForkSharpProjected (amp incoming paired axisRow)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonSeparatedPrefixMovingHighGrades (above)
variable {a u e:ℕ}{v:Rails h k (u+a) e}

def bill (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)(φ:Rarity D)(ψ:Rarity Q.D)
    (X:Q.Rider)(y dist r Bφ Bψ:ℝ)(older:ℕ):ℝ:=
  let Z:=epoch Y.vesselsC older Y.ceilC
  let Z₁:=max Z (max ψ.radius |y|)
  let nearFee:=BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^(u+a)*(Bφ*(C₀.buy Z*Y.fuel)))
  let farFee:=(hardCash e (u+a) C C C H Q).buy Z₁*(Bψ*fee Q e X)
  let residue:=C₁.buy Z*(coinMat (k+Q.h) e*nearFee*farFee)
  let joins:=(16*r)^u*(dist⁻¹)^a*((5*r)^4*(9^(u+a)*(Bφ*Y.fuel)))*coupon Q X e (u+a) r Bψ
  residue+Z*(joins*C₂.buy Z)

def contrast (Y:CutsP H T p v C C C C)(Q:SealR G)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(older:ℕ)(legs:Fin 0→YForest G):Cost:=
  reading (paired Y Q ψ X y o older k (incoming Y φ y o)).2 legs-
    ∑j,clock Y.ax Y.tx Y.N Y.m older (dose Y (amp Y) j)*reading (axisRow Y Q φ ψ X y o older j).2 legs

theorem original (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)
    (paid:WilsonMovingForkSharpMaster.Paid Y Q C₀ C₁ C₂)(ticket:PassportC H Y.vesselsC Q C C)
    (room:Q.h≤k)(older m:ℕ)(gate:Y.vesselsC.anchor≤older)(before:older≤Y.m)
    (φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y dist r Bφ Bψ:ℝ)(o:CellR)(own:Amplitude φ Bφ)(peer:Amplitude ψ Bψ)
    (clear:ClearDay φ ψ dist)(pos:0<dist)(nearBox:φ.radius+|y|+1≤r)(farBox:ψ.radius+|y|+1≤r)
    (legs:Fin 0→YForest G):
    let T₀:=paceT Y.ax.S m Y.m
    let scale:=paceT Y.ax.S m Y.ceilC
    let wage:=bill Y Q C₀ C₁ C₂ φ ψ X y dist r Bφ Bψ older
    let row:=fun j=>PowerSeries.coeff j (contrast Y Q φ ψ X y o older legs)
    (∀j≤e,‖row j‖≤T₀^(-((h:ℝ)+1/4))*(scale^((h:ℝ)+1/4)*wage)) ∧
      ∀(J:ℕ)(g:ℝ),0 ≤ g → g ≤ 1 → ‖above J e g row‖≤((e+1:ℕ):ℝ)*g^(J+1)*((T₀^h)⁻¹*(scale^h*wage)):=by
  intro T₀ scale wage row
  let ratio:=paceT Y.ax.S Y.m Y.ceilC
  let gain:=WilsonMovingForkSharpIncome.gain Y
  have sold:=paid older gate before φ ψ X y dist r Bφ Bψ o own peer clear pos nearBox farBox legs
  let Z:=whole Y Q φ ψ X y o older Y.i
  have eqn:contrast Y Q φ ψ X y o older legs=reading Z.2 legs:=
    WilsonMovingForkSharpProjected.original Y Q ticket room φ ψ X y o older before legs
  have actual : row=(fun j=>Z.2 j 0 legs):=by
    funext j
    change PowerSeries.coeff j (contrast Y Q φ ψ X y o older legs)=_
    rw [eqn]
    simp only [WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk]
  rw [actual]
  change (∀j≤e,‖Z.2 j 0 legs‖≤(ratio^h*gain)*wage) ∧ _ at sold
  constructor
  · intro j hj
    apply (sold.1 j hj).trans_eq
    change ((paceT Y.ax.S Y.m Y.ceilC)^h*WilsonMovingForkSharpIncome.gain Y)*wage=_
    rw [WilsonMovingForkSharpRuler.capture Y m,mul_assoc]
  · intro J g gp small
    have budget:0≤wage:=nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (sold.1 0 (Nat.zero_le _)))
      (mul_pos (pow_pos (pace_pos ..) _) (trail_pos ..))
    have saved:=WilsonMovingForkSharpRuler.unit Y
    have use:=mul_le_of_le_one_right (pow_nonneg (pace_pos Y.ax.S Y.m Y.ceilC).le h) saved
    calc
      _≤((e+1:ℕ):ℝ)*g^(J+1)*((ratio^h*gain)*wage):=sold.2 J g gp small
      _≤((e+1:ℕ):ℝ)*g^(J+1)*(ratio^h*wage):=mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right use budget) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg gp _))
      _=_:=by dsimp only [ratio,T₀,scale];rw [WilsonMovingForkSharpRuler.ordinary Y m];ring

end YM.Integration.WilsonMovingForkSharpRows
