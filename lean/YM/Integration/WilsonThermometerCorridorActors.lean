import YM.Integration.WilsonThermometerCorridorCharge
import YM.Integration.WilsonThermometerMarchFaces

/- A single genuine original pretest fare works for all three located physical
   legs throughout the measured corridor before their previously funded start. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorActors
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

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(t:ℕ)(ht:1≤t):
    ∀ᶠ b:ℕ in atTop,∀ f N p (_:b≤f)(fn:f≤N)(o:Fin 3→Site ((CF).side N p))
      (V:(i:Fin 3)→Sight (CF) (d i) p)(Q:(i:Fin 3)→Emblems (CF) (d i))
      (_:∀i,Enrolled R.makes R.doors (B) f N p (d i) (digits R N p (o i)) (V i) (Q i))
      (y:(i:Fin 3)→Palette (CF) (d i)),
      let z:=fun i=>WilsonThermometerMarchSource.reduce (y i)
      let w:=radius R t b f
      0<w ∧ w≤radius R t f f ∧ w⁻¹≤β f^(t+(f-b)) ∧
      ∃ (actors:∀j,Fin 3→Three G ((CF).side j p))(coins:ℕ→Fin 3→ℝ),
        (∀j,f≤j → j≤N → ∀i,actors j i=state (k:=f) R (V i) (Q i) (z i) (o i) j) ∧
        (∀j,b≤j → ∀jf:j<f,∀i,Ride ((A).clock.op j p)
          (location R (o i) (j+1)) (location R (o i) j) (R.doors N p j (jf.trans_le fn))
          1 (actors (j+1) i) (actors j i) (coins j i)) ∧
        ∀j,b≤j → j<f → ∀i,0≤coins j i ∧ 2*w*coins j i≤1:=by
  choose a pos caps using fun i:Fin 3=>Cap.cost (line (primaryLetter (d i))) (d i+2)
  let u:ℝ:=1+∑ i,a i
  have up:0<u:=by dsimp [u];linarith [Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>(pos i).le)]
  have test (i:Fin 3):Cap (d i+2) (line (primaryLetter (d i))) u:=by
    apply (caps i).increase
    dsimp [u];linarith [Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(pos j).le) (Finset.mem_univ i)]
  have awake:∀ᶠ b:ℕ in atTop,∀i:Fin 3,Awake (C:=(CF)) R.doors (B) b (d i):=
    Filter.eventually_all.mpr fun i=>(WilsonThermometerOffsetLedger.original R simple shop (d i)).mono fun _ h=>h.1
  filter_upwards [awake,WilsonThermometerOwnOffsetRadii.paid R simple 16 t,
      Many.theta_up (C:=(CF)) (max 1 (2*u)) simple] with b aw capital hot f N p bf fn o V Q members y
  dsimp only
  let z:=fun (i:Fin 3)=>WilsonThermometerMarchSource.reduce (y i)
  let ν:=fun (i:Fin 3)=>WilsonCapturedPrimaryWardRetimed.ratio (CF) f b (d i)
  choose U r init enrolled growth upper rides using fun (i:Fin 3)=>
    WilsonThermometerCorridorRides.original R (members i) fn bf (aw i) (z i)
  let actors:=fun (j:ℕ) (i:Fin 3)=>ν i • state (k:=b) R (U i) (r i) (init i) (o i) j
  let coins:=fun (j:ℕ) (i:Fin 3)=>if h:b≤j then ‖ν i‖*charge R (r i) (init i) h u else 0
  let w:=radius R t b f
  let X:=span R b f
  have Xpos:=span_pos R b f
  have Xone:=span_one R bf
  have wp:=radius_pos R t b f bf
  have scale:0<β f^t:=pow_pos (WardBin.hot _ _) _
  have wallet:=capital f bf
  have revert:w≤radius R t f f:=by
    rw [radius_start,←one_div]
    change w≤1/(β f)^t
    apply (le_div_iff₀ scale).mpr
    exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right wp.le (one_le_pow₀ Xone)) scale.le).trans wallet
  refine ⟨wp,revert,WilsonThermometerMarchFaces.slot R simple t b f bf,actors,coins,?_,?_,?_⟩
  · exact fun j fj jn i=>upper i j fj jn
  · intro j bj jf i
    dsimp only [actors,coins,ν]
    rw [dif_pos bj]
    exact rides i j bj (jf.trans_le fn) u (test i)
  · intro j bj jf i
    dsimp only [coins]
    rw [dif_pos bj]
    have ride:=rides i j bj (jf.trans_le fn) u (test i)
    refine ⟨ride.nonneg,?_⟩
    have ready: size (init i) ≤ X^(d i+1):=(growth i).trans (calc
      _ ≤ X*X^(d i)*size (z i):=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (meter R bf) (pow_nonneg Xpos.le _)) (size_ge _)
      _ ≤ X*X^(d i)*1:=mul_le_mul_of_nonneg_left (WilsonThermometerMarchSource.small _) (mul_nonneg Xpos.le (pow_nonneg Xpos.le _))
      _=X^(d i+1):=by rw [pow_succ];ring)
    have inner:=pow_le_pow_right₀ Xone (show 2*d i+4≤16 by fin_cases i <;> decide)
    have earns:= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left inner wp.le) scale.le).trans wallet
    have funds:=hot.trans (Many.beta_le' (C:=(CF)) simple bf)
    have atFine:2*u≤β f^t:=((le_max_right 1 _).trans funds).trans
      (by simpa only [pow_one] using (pow_le_pow_right₀ ((le_max_left 1 _).trans funds) ht))
    exact WilsonThermometerCorridorCharge.radius_paid R (enrolled i) (init i) bj jf fn ready earns up.le atFine

end YM.Integration.WilsonThermometerCorridorActors
end
