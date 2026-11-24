import YM.Integration.WilsonIndependentCollarLocatorAmount
import YM.Integration.WilsonOriginalCensusDatedMaterial

/-! The exact word in a named filed census has the paid rooted angular
rows and the mounted group-word intensity of its particular relative
placement, including the accumulated connected scalar. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarMaterialIntensity
open Finset Function Lattice RG Wilson Precision QuadraticLocal QuadraticLocal.Earn Marker Multi Push Push.PriceCompiler
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Express WilsonOlderFreshConnectedRobe WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedBirth WilsonOriginalCensusDatedMaterial WilsonRegisteredPairUnaryWallet
open WilsonOlderFreshGraphPointWallet (point)
open PhysicalNext.Repeat.Legato Push.AbsoluteSums Push.Local
open scoped Classical BigOperators
variable {G:Gauge}{n N m q:ℕ}{k:Fin n→ℕ}{σ:ℝ}{side:Side}{P:Passport side (Fin n)}{I:Type}
  {R:Run G}{B:I→Binder P (Stock.census (Fin n))}(H:Material R N m q k σ B)(z:I)
local notation "s" => (B z).mode.val
local notation "c" => H.pin z
local notation "ν" => R.family.path.levels.clock.hatBeta m^H.allowance * H.amplitude^(s).card
local notation "reach₀" => feeH (toe (s) (c) (H.root z) (H.frill z)) (c) (s)

def price:ℝ:=∑a:Fin (q+1),cost (s) (mass k (s)) a (H.source z) (ν)

theorem jets (o:Cover)(a:Fin (q+1))(r:Fin (mass k (s)+a.val+1)):
    Rooted H.realm H.start H.prior (s) (c) (mass k (s)) N (32*σ) (ν) o a.val r:=
  (H.paid N H.available (s) (c) H.amplitude H.prior (H.included z) (H.marked z)
    H.nonneg H.lower).2 o a.val (by have :=a.isLt;omega) r

theorem original:
    Real.exp ((32*σ)*(reach₀))*WilsonIndependentCollarSlateIntensity.amount (words H z) (B z).center ≤ price H z:=by
  let T:=fun u:Frill (s) (c)=>issued R H.realm H.start H.paid N (c) H.prior (H.included z)
    (H.marked z) H.nonneg H.lower (H.positive z) H.radius.le (H.root z) (H.source z) u
  let map:(words H z).Roster→Σ u:Frill (s) (c),(T u).Roster:=fun r=>⟨H.frill z,r⟩
  have inj:Injective map:=fun x y h=>eq_of_heq (Sigma.mk.inj h).2
  have all:=WilsonIndependentCollarLocatorRoster.original R H.realm H.start H.paid (c) H.prior (H.included z)
    (H.marked z) H.nonneg H.lower (H.positive z) H.radius.le (H.root z) (H.source z) (fun _=>(B z).center)
  have selected:=budget_pull map inj all
  calc
    _=∑'r:(words H z).Roster,Real.exp ((32*σ)*(reach₀))*(((words H z).rows (point (B z).center) disk) r).height σ:=
      (tsum_mul_left ..).symm
    _≤price H z:=selected.2.2

theorem mounted (reserve:ℕ)(record:(B z).length ≤ reserve+32*(reach₀)):
    Real.exp (σ*(B z).length)*WilsonIndependentCollarSlateIntensity.amount (words H z) (B z).center ≤
      Real.exp (σ*reserve)*price H z:=by
  have hold:((B z).length:ℝ) ≤ (reserve:ℝ)+32*((reach₀):ℝ):=by exact_mod_cast record
  have pay:Real.exp (σ*(B z).length)≤Real.exp (σ*reserve)*Real.exp ((32*σ)*(reach₀)):=by
    rw [←Real.exp_add,Real.exp_le_exp]
    exact (mul_le_mul_of_nonneg_left hold H.radius.le).trans_eq (by ring)
  have pos:0≤WilsonIndependentCollarSlateIntensity.amount (words H z) (B z).center:=
    (tsum_nonneg (WilsonIndependentCollarSlateIntensity.spent (words H z) (B z).center H.radius.le).1)
  exact (mul_le_mul_of_nonneg_right pay pos).trans ((mul_assoc ..).le.trans
    (mul_le_mul_of_nonneg_left (original H z) (Real.exp_pos _).le))

end YM.Integration.WilsonIndependentCollarMaterialIntensity
end
