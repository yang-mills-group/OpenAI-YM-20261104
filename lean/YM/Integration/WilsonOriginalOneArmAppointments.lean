import YM.Integration.WilsonOriginalOneArmMaterialPayer
import YM.Integration.WilsonOriginalOneArmCanonicalPayer

set_option autoImplicit false
namespace YM.Integration.WilsonOriginalOneArmAppointments

open Lean Meta Elab Term
/-- Give a booked row exactly the input telescope of its original payer. Its result
index names the original course, two dates, whole filed laws and signed fee. -/
local elab "booking% " payer:term " yielding " receipt:term : term => do
  let source ← Term.elabTerm payer none
  let wrap ← Term.elabTerm receipt none
  Meta.forallTelescope (←Meta.inferType source) fun inputs issued =>
    Meta.mkForallFVars inputs (mkApp wrap issued)

inductive Material : Prop → Prop where
  | posted : booking% (@WilsonOriginalOneArmMaterialPayer.original) yielding Material

inductive Canonical : Prop → Prop where
  | posted : booking% (@WilsonOriginalOneArmCanonicalPayer.original) yielding Canonical

theorem material {p:Prop} (book:Material p):p:=by
  cases book with
  | @posted G n q m j N per k grades R hk D Q π Γ Ψ course φ books base ahead dims V draw rate allowance digits test κ pt top seed sites L U low high wallet tags later valid shelf opL lessonL opU lessonU tollL tollU tolL tolU lowerFile upperFile rows simple rentOrder p pieces stage requested demand enrolled depth age sized below above loSeats hiSeats ready paidAge charge up down early small tube front owned teacher pass month quiet read τ cash funded legalU legalL rates within target enough ceiling late gross weight opened C paid diameter covered selected credit lawU lawL way hospital warm uPos lPos df frame section_ group ticket s b floor older np cost P f d tariff grade period reserve station support η ep opening =>
    exact @WilsonOriginalOneArmMaterialPayer.original G n q m j N per k grades R hk D Q π Γ Ψ course φ books base ahead dims V draw rate allowance digits test κ pt top seed sites L U low high wallet tags later valid shelf opL lessonL opU lessonU tollL tollU tolL tolU lowerFile upperFile rows simple rentOrder p pieces stage requested demand enrolled depth age sized below above loSeats hiSeats ready paidAge charge up down early small tube front owned teacher pass month quiet read τ cash funded legalU legalL rates within target enough ceiling late gross weight opened C paid diameter covered selected credit lawU lawL way hospital warm uPos lPos df frame section_ group ticket s b floor older np cost P f d tariff grade period reserve station support η ep opening

theorem canonical {p:Prop} (book:Canonical p):p:=by
  cases book with
  | @posted G R simple m j N per k hk D Q π Γ Ψ course φ books base cut op lesson ahead n d q hd y cells order shelf S' a' rows lower rentLimit origin x same upper adopts s charges rentOrder target C precision breadthCap lowOrder way pass month hospital warm nn' calendar pt tags length σ₀ L active matched lowPlaced lowNames lowInk graded wallet positive depth lowOrderEq highCap lowCap lens matchedTests menu go board near budget b K floor older finer admitted loadN cost P f gradeBudget np load_ok tariff grade period prior support atStation df frame section_ group ticket η ep when_ qc deep age hard one more previous =>
    exact @WilsonOriginalOneArmCanonicalPayer.original G R simple m j N per k hk D Q π Γ Ψ course φ books base cut op lesson ahead n d q hd y cells order shelf S' a' rows lower rentLimit origin x same upper adopts s charges rentOrder target C precision breadthCap lowOrder way pass month hospital warm nn' calendar pt tags length σ₀ L active matched lowPlaced lowNames lowInk graded wallet positive depth lowOrderEq highCap lowCap lens matchedTests menu go board near budget b K floor older finer admitted loadN cost P f gradeBudget np load_ok tariff grade period prior support atStation df frame section_ group ticket η ep when_ qc deep age hard one more previous

end YM.Integration.WilsonOriginalOneArmAppointments
