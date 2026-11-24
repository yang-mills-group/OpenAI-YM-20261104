import YM.Integration.WilsonThermometerUnitFilingCoverAudition

/-! Read the exact suspension of the one-name capture directly from its original enrolled rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverNotice
open Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry RegulatorIR RegulatorIR.Profiles
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{o:Passport n Unit}{J:Census Unit}{I X:Type}
  (M:I→Row o J G X) {w:Unit→ℝ}{grade:Unit→ℕ}{σ C:ℝ}{ord cap H:ℕ}
  (stock:Scene.Armada M w grade σ C ord cap H)

include stock in
theorem degree (i:I):(M i).lamp.toll=grade ():=by
  have mode:(M i).mode.val=Finset.univ:=by
    ext v
    simp only [Finset.mem_univ,iff_true]
    rw [show v=(M i).binder.front from Subsingleton.elim ..]
    exact (M i).binder.east
  have actual:=(stock.purchases.usable i).2
  rw [mode] at actual
  simpa using actual

include stock in
theorem native (s:Finset I)(t:X)(a:ℂ→L[ℝ]ℝ):
    LocalStamp (WilsonThermometerUnitFilingCoverAudition.bank M s t a) (grade ()+1):=by
  apply WilsonThermometerUnitFilingCoverStock.original
  intro i _
  rw [degree M stock i]

end YM.Integration.WilsonThermometerUnitFilingCoverNotice
