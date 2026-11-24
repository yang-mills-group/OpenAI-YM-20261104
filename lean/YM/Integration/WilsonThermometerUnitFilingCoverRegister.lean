import YM.Integration.WilsonThermometerUnitFilingCoverShift
import YM.Integration.WilsonThermometerUnitFilingCoverNotice
import YM.Integration.WilsonThermometerUnitFilingCoverCurrency
import YM.RegulatorIR.Uniform.Claim

/-! The earned finite parts of a captured source give one claim on the actual older course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverRegister
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry
open RegulatorIR Taping Budget Budget.Packet Prim Profiles Halo Ledger Ledger.Sky Oracle Uniform
open WilsonThermometerUnitFilingCoverAudition
open scoped Classical BigOperators ENNReal

structure Submission (G:Gauge) where
  n:Side
  o:Passport n Unit
  J:Census Unit
  I:Type
  X:Type
  rows:I→Row o J G X
  part:Finset I
  test:X
  read:ℂ→L[ℝ]ℝ
  short:‖read‖≤1
  rad:Unit→ℝ
  grades:Unit→ℕ
  σ:ℝ
  cost:ℝ
  order:ℕ
  cap:ℕ
  seats:ℕ
  bought:Scene.Armada rows rad grades σ cost order cap seats
  width:0<σ
  positive:0<rad ()

variable {G:Gauge}
def field (S:Submission G):Portrait G:=bank S.rows S.part S.test S.read

theorem stamp (S:Submission G){h:ℕ}(paid:S.grades ()+1=h): LocalStamp (field S) h:=by
  rw [←paid]
  exact WilsonThermometerUnitFilingCoverNotice.native S.rows S.bought S.part S.test S.read

variable {W:Type}{steps:W→ℕ}{sides:Page steps→Side}(Z:Circuit steps sides)
  {K:KernelChoices}(scheme:Program K)(branches:∀ P:Patch,P.Branches K G)(units:Page steps→Binding.Scale)
local notation "L" => Z.dialect scheme G branches units
variable (T:Ledger.Sky.Accounts (Z.dialect scheme G branches units))
  {m:Uniform.Meter W}{p b h:ℕ}(P:Ledger.Sky.Primitive (Z.dialect scheme G branches units) m p b)
  (k:Choice steps)(S:W→Submission G)(paid:∀v,(S v).grades ()+1=h)
local notation "report" => WilsonThermometerUnitFilingCoverEra.filed (L) T P k (fun v=>field (S v))
  (fun v=>stamp (S v) (paid v))

theorem original (meter:Uniform.Meter W)(β:W→ℝ)(late:∀v,Real.exp 1≤β v)
    (width:∀v,Real.exp ((S v).σ⁻¹^2)≤β v){δ:ℝ}(small:0<δ)(e r u:ℕ):
    Claim meter (fun v=>(L).coverQ (fun _=>0) u (k.choose v))
      (fun v=>ENNReal.ofReal (WilsonThermometerUnitFilingCoverInvoice.invoice G (e+h) u δ (β v)
        (S v).cost ((S v).rad ())))
      (fun v=>(report).main (Page.opening k.after.spans v) e r):=by
  refine ⟨fun _=>1,Uniform.Poly.oneQ meter,fun v=>?_⟩
  rw [one_mul]
  exact WilsonThermometerUnitFilingCoverShift.original (S v).rows (S v).part (S v).test
    (S v).read Z scheme branches units T P k (fun x=>field (S x)) (fun x=>stamp (S x) (paid x))
    v rfl (S v).bought (S v).width small (late v) (width v) (S v).positive (S v).short e r u

end YM.Integration.WilsonThermometerUnitFilingCoverRegister
