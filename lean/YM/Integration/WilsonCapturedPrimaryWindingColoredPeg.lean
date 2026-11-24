import YM.Integration.WilsonCapturedPrimaryWindingBanks
import YM.Integration.WilsonEmittedFiledDeckFare

/-! Real and imaginary material tables determine the entire complex mixed Wilson
jet at a finite regulator. Only the measured source needs a smooth group germ. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingColoredPeg
open Function Finset Lattice Wilson RG Marker Stationary
open Comparison.RG02 Comparison.RG02.Adjacent
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Diagram
open RegulatorIR.Budget RegulatorIR.Budget.Packet
open WilsonIndependentCapturedAngularWinding WilsonIndependentCapturedFiledDirections
open WilsonEmittedAngularJointFare WilsonEmittedFiledMixedWindow WilsonEmittedFiledDeckFare
open private difference from YM.Integration.WilsonEmittedFiledThermalGerm
open scoped BigOperators Classical ContDiff Topology
variable {G:Gauge}{n:Side}{U:Type}[DecidableEq U]{C:Census U}
local notation "E" => Stationary.Link G n
local notation "I" => SiteSlot G n
local notation "H" => WilsonEmittedWordJointFare.Chart G n
local notation "colors" => (edgeColor (G:=G) (n:=n))

def restore (G:Gauge)(n:Side) : ℝ×(Stationary.Link G n) →L[ℝ] WilsonEmittedWordJointFare.Chart G n :=
  (ContinuousLinearMap.fst ℝ ℝ (Stationary.Link G n)).prod
    ((edgeColor (G:=G) (n:=n)).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ (Stationary.Link G n)))

theorem census (F:H→ℂ) (d:ℕ) (h:ContDiffAt ℝ d F 0)
    (b:(r:ℕ)→(Fin r→I)→ℂ) (heard:∀a:E,Assembly.jet F d (1,colors a)=held b (fun v i=>(v i:ℂ)) d a):
    ∑i:Fin d→WilsonEmittedRootedJetWage.Slot G n,
        ‖iteratedFDeriv ℝ d F 0 (WilsonEmittedRootedJetWage.peg G n ∘ i)‖≤(d.factorial:ℝ)*mass b d:=by
  let f:=F∘restore G n
  have h₀:ContDiffAt ℝ d F (restore G n 0):=by simpa only [map_zero] using h
  have h₁:ContDiffAt ℝ d f 0:=h₀.comp 0 (restore G n).contDiff.contDiffAt
  have eq:F=f∘joint G n:=by
    funext z
    change F z=F (z.1,colors ((colors).symm z.2))
    rw [ContinuousLinearEquiv.apply_symm_apply]
  change _≤_
  conv_lhs => rw [eq]
  rw [WilsonCapturedPrimaryWindingBanks.physical f d h₁]
  apply WilsonCapturedPrimaryWindingPeg.germ f h₁ b
  intro a
  exact (Assembly.jet_continuous_right (restore G n) h₀ (1,a)).trans (heard a)

theorem realRow (V Z:Bulk.Colors C G n)(left right:UnitCost)(u:U)(A B:Orders (I))
    {e cap pole:ℕ}(inside:e≤cap)
    (actual:Booth.Arm.Single left V A u cap pole)(prescribed:Booth.Arm.Single right Z B u cap pole)(a:E):
    row left V u e a-row right Z u e a=
      held (fun r x=>((A e r x-B e r x:ℝ):ℂ)) (fun v i=>(v i:ℂ)) (e+pole) a:=by
  have read (T:Bulk.Colors C G n)(c:UnitCost)(K:Orders (I))(file:Booth.Arm.Single c T K u cap pole):
      row c T u e a=value (K e) (e+pole) a:=by
    have earned:See.noseC C u c T e (Stationary.arm G n 1 a)=
      Booth.Uniforms.cuff K pole e (Stationary.arm G n 1 a):=file.earned e inside _
    unfold row
    rw [earned,Booth.Uniforms.cuff,Binding.flavor_lo]
    rfl
  rw [read V left A actual,read Z right B prescribed,difference]

theorem two (F:H→ℂ) {e pole cap:ℕ} (u:U)(left right:UnitCost)
    (V Z:Bool→Bulk.Colors C G n)(A B:Bool→Orders (I))(inside:e≤cap)
    (actual:∀k,Booth.Arm.Single left (V k) (A k) u cap pole)
    (prescribed:∀k,Booth.Arm.Single right (Z k) (B k) u cap pole)
    (h:ContDiffAt ℝ (e+pole) F 0)
    (read:∀a:E,Assembly.jet F (e+pole) (1,colors a)=
      (row left (V false) u e a-row right (Z false) u e a)+
      (row left (V true) u e a-row right (Z true) u e a)*Complex.I):
    let b:=fun k r x=>(((A k) e r x-(B k) e r x:ℝ):ℂ)
    (∑i:Fin (e+pole)→WilsonEmittedRootedJetWage.Slot G n,
        ‖iteratedFDeriv ℝ (e+pole) F 0 (WilsonEmittedRootedJetWage.peg G n ∘ i)‖)≤
        ((e+pole).factorial:ℝ)*(mass (b false) (e+pole)+mass (b true) (e+pole)):=by
  intro b
  let money:=fun r x=>b false r x + b true r x*Complex.I
  apply (census F (e+pole) h money ?_).trans
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    unfold mass
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro r _
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro x _
    have sum:=norm_add_le (b false r x) (b true r x*Complex.I)
    simpa only [norm_mul,Complex.norm_I,mul_one] using sum
  · intro a
    rw [read a,realRow _ _ _ _ _ _ _ inside (actual false) (prescribed false),
      realRow _ _ _ _ _ _ _ inside (actual true) (prescribed true)]
    simp only [money,b,held,sum_mul,←sum_add_distrib,add_mul]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro x _
    ring

end YM.Integration.WilsonCapturedPrimaryWindingColoredPeg
end

