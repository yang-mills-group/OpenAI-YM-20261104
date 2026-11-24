import YM.Integration.WilsonIndependentCollarOpticalOrdinary
import YM.Integration.WilsonIndependentCollarPrintIncome

/-! Print the complete prescribed source after its actual unsummed child
history. All support and term salaries are those of the elected path compiler. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOpticalPrint
open Function Finset Lattice RG Precision Wilson Exterior
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonReceivedFixedDigitHistory
open scoped BigOperators Classical
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e:ℕ}

theorem printed (Q:Realm G (e+1) Credit.leanC)
    (N:ℕ) (cell:Digits Q.draws ι) (Y:Outerm G D) (well:Wellness k Y) (B:ℝ) (hB:0≤B)
    (days m:ℕ) (hm:Q.anchor ≤ m) (cut:m+days≤N)
    (regular:Uniform Q (itinerary Q.draws Q.paid k N cell days m Y) m hm B)
    (S:Finset ι) (front:ι) (atFront:front∈S) (y:ι → Cover) (b rank:ℕ) (size:S.card≤b)
    (rnk:mass k S ≤ rank) (tickets:Insure b rank Q Credit.leanC):
    let bank:=itinerary Q.draws Q.paid k N cell days m Y y S
    let print:=sphere bank (mass k S) (e+1) front y
    let width:=VestS b rank Q m hm
    let price:=VestZ b rank Q m hm*B^S.card
    Rains print (e+1) width (price*Real.exp (-(Vσ Q m hm)/2*realmSize S y)) ∧
      tenure print S y front (e+1) width (price*Real.exp (-(Vσ Q m hm)/4*realmSize S y)) ∧
      (∀ j<e+1,let filed:=shifted (baton print (e+1)) (y front)
        Auth (mass k S) filed ∧ filed.2 j=bank.2 j ∧
          ∀ n r,filed.1 n j r=Carp.plume (bank.2 j r) n) ∧
      width⁻¹≤Q.cash Credit.leanC m ∧ VestZ b rank Q m hm≤Q.cash Credit.leanC m:=by
  let Z:=itinerary Q.draws Q.paid k N cell days m Y
  have wardrobe:Wellness k Z:=sound Q.draws Q.paid k N cell Q.hG Q.green Y well days m cut
  have salary:0≤B^S.card:=by positivity
  have printed:=posting (tickets.proof m hm) y (Z y S) atFront rnk size _ salary
    (wardrobe.level' y S) (fun j hj r=>(regular y S j (by omega) r).shave (min_le_right ..))
    (le_refl (e+1))
  exact ⟨printed.1,printed.2.1,printed.2.2,tickets.labor m hm⟩

end YM.Integration.WilsonIndependentCollarOpticalPrint
end

