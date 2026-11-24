import YM.Integration.WilsonThermometerCorridorFourFaces
import YM.Integration.WilsonThermometerRegisteredTripleRoom
import YM.Integration.WilsonThermometerCorridorLawn
/- The two true taps of the complete named separated incoming R gallery at
   its exact reference f use the affordable rides from the earlier grouped
   date. The continuation below f has the same actors on every original mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorCash
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta
local notation "d" => WilsonThermometerFundedWeakCells.degree
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "slots" => (Stock.census (Fin 3))

local notation "CF"=>R.family

open RG05Readout.Pantry WilsonThermometerOwnOffsetJoint

open QuadraticLocal
open MergeProof.Ribbons Ribbons.ManyCopies.Muster
open WilsonThermometerPepperFace
local notation "V"=>Unit×Fin 3

theorem aperture {H η w α:ℝ}(hot:1≤H)(wp:0<w)(heat:0<η)(small:η≤1)
    (book:(η*(η*w)/Real.exp α)⁻¹≤H^6*w⁻¹):Real.exp α≤H^6:=by
  have e:=Real.exp_pos α
  calc _ = (η*(η*w)/Real.exp α)⁻¹*(η*(η*w)) :=by field_simp
       _ ≤ (H^6*w⁻¹)*(η*(η*w)) :=mul_le_mul_of_nonneg_right book (by positivity)
       _ = H^6*(η*η) :=by field_simp
       _ ≤ _ :=mul_le_of_le_one_right (by positivity) (by nlinarith only [heat,small,mul_nonneg heat.le (sub_nonneg.mpr small)])

theorem one (w:(V)→ℝ)(i:(V))(l debt:ℕ){H η α:ℝ}(hot:1≤H)(yp:0<η)(wp:0<w i)
    (restored:(w i)⁻¹≤H^debt)(income:η⁻¹≤H^2)(quoted:Real.exp α≤H^6):
    (Fibers.Salt.tow (fun i=>η*w i) α (η/3) l i)⁻¹≤3*H^(4+debt+6*l):=by
  have gross:=Real.exp_pos α
  have hp:0<H:=zero_lt_one.trans_le hot
  unfold Fibers.Salt.tow
  calc _ = 3*(η⁻¹*(η⁻¹*((w i)⁻¹*(Real.exp α)^l))) :=by
            rw [mul_comm α _,Real.exp_nat_mul]
            field_simp
       _ ≤ 3*(H^2*(H^2*(H^debt*(H^6)^l))) :=by
          gcongr
       _ = _ :=by rw [pow_add,pow_add,pow_mul];ring

theorem group {n:Side}(P:Rep G n)(anchor:(V))(w:(V)→ℝ)(l debt:ℕ){H η:ℝ}
    (hot:1≤H)(yp:0<η)(wp:∀i,0<w i)(restored:∀i,(w i)⁻¹≤H^debt)(income:η⁻¹≤H^2)
    (quoted:Real.exp (P.p.supportExponent+1/2)≤H^6):
    1/(WilsonThermometerWeakMixedGrouping.radius (atSite anchor) P 3 l η (fun i=>η*w i) ())≤
      27*H^(3*(4+debt+6*l)):=by
  let L:=atSite anchor
  let cap:=3*H^(4+debt+6*l)
  have hcap:1≤cap:=by
    have po:1≤H^(4+debt+6*l):=one_le_pow₀ hot
    dsimp only [cap]
    linarith
  have card:(L.contents ()).card ≤ 3:=by
    have h:=Finset.card_le_univ (L.contents ())
    simpa only [Fintype.card_prod,Fintype.card_unique,Fintype.card_fin,one_mul] using h
  let fee:=Fibers.Salt.tow (fun i=>η*w i) (P.p.supportExponent+1/2) (η/3) l
  change 1/(∏i∈L.contents (),fee i)≤_
  rw [one_div,←Finset.prod_inv_distrib]
  calc _ ≤ ∏ _i∈L.contents (),cap:=Finset.prod_le_prod
              (fun i _=>by have h:=wp i;dsimp [fee,Fibers.Salt.tow];positivity)
              (fun i _=>one w i l debt hot yp (wp i) (restored i) income quoted)
       _ ≤ cap^3 :=by rw [prod_const];exact pow_le_pow_right₀ hcap card
       _ = _ :=by dsimp only [cap];rw [Nat.mul_comm 3 (4+debt+6*l),pow_mul,mul_pow];norm_num

end YM.Integration.WilsonThermometerCorridorCash
end
