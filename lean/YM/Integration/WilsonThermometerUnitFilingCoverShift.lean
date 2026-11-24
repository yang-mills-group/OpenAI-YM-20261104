import YM.Integration.WilsonThermometerUnitFilingCoverShare
import YM.RegulatorIR.Oracle.Arrange

/-! Use the real geometric reporter's rooted mark at capture, with its original quiet history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverShift
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry
open RegulatorIR Taping Budget Budget.Packet Budget.Tuple Prim Profiles Halo Ledger Ledger.Sky Oracle
open WilsonThermometerUnitFilingCoverInvoice WilsonThermometerUnitFilingCoverAudition
open scoped Classical BigOperators ENNReal
variable {G:Gauge}{n:Side}{o:Passport n Unit}{J:Census Unit}{I X:Type}
  (M:I→Row o J G X)(s:Finset I)(x:X)(a:ℂ→L[ℝ]ℝ)
  {w:Unit→ℝ}{grades:Unit→ℕ}{σ C β δ:ℝ}{ord cap H:ℕ}
  {W:Type}{steps:W→ℕ}{sides:Page steps→Side}(Z:Circuit steps sides)
  {K:KernelChoices}(scheme:Program K)(branches:∀ P:Patch,P.Branches K G)(units:Page steps→Binding.Scale)
local notation "L"=>Z.dialect scheme G branches units
variable (T:Ledger.Sky.Accounts (Z.dialect scheme G branches units))
    {m:Uniform.Meter W}{p b h:ℕ}(P:Ledger.Sky.Primitive (Z.dialect scheme G branches units) m p b)(k:Choice steps)
    (F:W→Portrait G)(law:∀ v,LocalStamp (F v) h)

include T P in
theorem original (v:W)(submitted:F v=bank M s x a)(stock:Scene.Armada M w grades σ C ord cap H)
    (seed:0<σ)(tiny:0<δ)(late:Real.exp 1≤β)(paid:Real.exp (σ⁻¹^2)≤β)(income:0<w ())(re:‖a‖≤1)
    (e r u:ℕ):
    markQ ((L).coverQ (fun _=>0) u (k.choose v))
      ((WilsonThermometerUnitFilingCoverEra.filed (L) T P k F law).main (Page.opening k.after.spans v) e r) ≤
      ENNReal.ofReal (invoice G (e+h) u δ β C (w ())):=by
  exact WilsonThermometerUnitFilingCoverShare.original M s x a
    (k.after.part (L) T P) F law v submitted stock seed tiny late paid income re
    ((L).hl (k.choose v)) ((L).radius_pos _) (le_max_right _ _) e r u

end YM.Integration.WilsonThermometerUnitFilingCoverShift
