import YM.Integration.WilsonThermometerUnitFilingCoverBalance
import YM.Integration.WilsonThermometerUnitFilingPinCharge
import YM.Integration.WilsonThermometerUnitFilingPinBirth

/-! The purchased angular wage at the submitted interior pin, uniformly in finite subrosters. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinBalance
open Finset Lattice RG Wilson Marker
open RegulatorIR Taping Budget Budget.Packet Prim Profiles Halo Ledger Ledger.Sky Oracle Uniform
open WilsonThermometerUnitFilingCoverRegister
open WilsonThermometerUnitFilingCoverCurrency (gross part sign)
open scoped Classical BigOperators ENNReal

variable {G:Gauge}{W:Type}{steps:W→ℕ}{sides:Page steps→Side}(Z:Circuit steps sides)
  {K:KernelChoices}(scheme:Program K)(branches:∀ P:Patch,P.Branches K G)(units:Page steps→Binding.Scale)
local notation "L" => Z.dialect scheme G branches units
variable (T:Ledger.Sky.Accounts (Z.dialect scheme G branches units))
  {m:Uniform.Meter W}{p b h:ℕ}(P:Ledger.Sky.Primitive (Z.dialect scheme G branches units) m p b)
  (k:Choice steps)(S:W→Submission G)(paid:∀v,(S v).grades ()+1=h)
local notation "report" => WilsonThermometerUnitFilingCoverEra.filed (L) T P k (fun v=>field (S v))
  (fun v=>stamp (S v) (paid v))


open RegulatorIR.Spatial RegulatorIR.Budget RegulatorIR.Budget.Packet
open WilsonThermometerUnitFilingPinBirth
def pin (center:W→Room)(v:W):Lattice.Cover:=nearest ((L).l (k.choose v)) (center v)
def shifted (center:W→Room)(v:W):Portrait G:=
  located (fun x=>field (S x)) (pin Z scheme branches units k center) v
include paid in
theorem checked (center:W→Room)(v:W):LocalStamp (shifted Z scheme branches units k S center v) h:=
  lawful (fun x=>field (S x)) (fun x=>stamp (S x) (paid x)) (pin Z scheme branches units k center) v
local notation "shiftedReport" c:max => WilsonThermometerUnitFilingCoverEra.filed (L) T P k
  (shifted Z scheme branches units k S c) (checked Z scheme branches units k S paid c)

theorem original (center:W→Room)(meter:Uniform.Meter W)(β g cash:W→ℝ)(late:∀v,Real.exp 1≤β v)
    (width:∀v,Real.exp ((S v).σ⁻¹^2)≤β v)
    (gp:∀v,0<g v)(cp:∀v,0≤cash v)(heat:∀v,β v*(g v)^2≤2)
    (d:ℕ)(income:∀v,(S v).cost/((S v).rad ())≤(1+cash v)/(g v)^d)
    (accuracy e r u:ℕ)(wanted:e≤accuracy):
    Claim meter (fun v=>(L).coverQ center u (k.choose v))
      (fun v=>ENNReal.ofReal (2*gross G h u accuracy*(1+cash v)/(g v)^(d+2)) * (2:ℝ≥0∞)^u)
      (fun v=>(shiftedReport center).main (Page.opening k.after.spans v) e r):=by
  obtain ⟨f,fo,enough⟩:=WilsonThermometerUnitFilingCoverBalance.original Z scheme branches units T P k S paid
    meter β g cash late width gp cp heat d income accuracy e r u wanted
  refine ⟨f,fo,fun v=>?_⟩
  let a:=k.choose v
  let ℓ:=(L).l a
  let z:=pin Z scheme branches units k center v
  let U:=(report).main (Page.opening k.after.spans v) e r
  have hl:0<ℓ:=(L).hl a
  have near:dist (center v) (Motion.slide ℓ z)≤(L).radius a:=by
    change halfwidth ℓ (center v) ≤ max 1 ℓ
    exact (halfwidth_le ℓ hl _).trans ((by linarith : ℓ/2≤ℓ).trans (le_max_right ..))
  have moved:=congrArg (fun A:Diagram.Orders (Prim.Foot G)=>A e r)
    (WilsonThermometerUnitFilingPinBirth.original (k.after.part (L) T P)
      (fun x=>field (S x)) (fun x=>stamp (S x) (paid x)) v (pin Z scheme branches units k center))
  change markQ (WilsonThermometerUnitFilingPinCharge.grid ℓ ((L).radius a) ((L).radius_pos a) u (center v)) ((shiftedReport center).main (Page.opening k.after.spans v) e r) ≤ _
  rw [show (shiftedReport center).main (Page.opening k.after.spans v) e r=Halo.echo (Halo.carryX z) U from moved]
  refine (WilsonThermometerUnitFilingPinCharge.original ℓ ((L).radius_pos a) u (center v) z near U).trans ?_
  exact (mul_le_mul' (enough v) (le_refl ((2:ℝ≥0∞)^u))).trans_eq (mul_assoc ..)

end YM.Integration.WilsonThermometerUnitFilingPinBalance
