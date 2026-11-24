import YM.Integration.WilsonMeasuredPublicEntranceTrialTail
/-! The tail deleted from any peer is heard against the true reached hard
slice, using the native cap on that slice divided by its own vacuum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceFiredTail
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Marker QuadraticLocal Extra.Histories Relay
open PhysicalNext PhysicalNext.Repeat Legato Work.G08
open WilsonMeasuredCoefficientTransport WilsonThermometerUnitFilingFieldRange WilsonOriginalAlternativeHearing
open WilsonMeasuredPublicEntranceCheapOrder WilsonMeasuredPublicEntranceTrialTail
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per f m d:ℕ}(top:f≤N)
  (W:Rep G (R.family.side f per))(same:W.eval=(R.family.path.rep N per f).eval)
  (h:Coefficient (R.family.labels.level d) (R.family.side f per))(o:Site (R.family.side f per))
  (x0:h.x=0)(r0:h.regular=0){C:ℝ}
  (actual:∀U,‖h.density o (R.family.localSection d) W U/(W.eval U:ℂ)‖≤C)
local notation "P" => R.family.path.rep N per f

include top same x0 r0 actual in
theorem original {V:Type*} (vs:List V)(a b:Config G (R.family.side f per)→V→ℂ)
    (cap δ:V→ℝ)(gross:∀U v,‖a U v‖≤cap v)(crop:∀U v,‖a U v-b U v‖≤δ v)
    (down:m≤f)(T:Config G (R.family.side m per)):
    ‖held R.family N per (fun U=>account h W U*((vs.map (a U)).prod-(vs.map (b U)).prod)) down T‖ ≤
      C*route cap (fun v=>cap v+δ v) δ vs:=by
  rw [normalized R.family N per R.makes top _ down]
  apply actualTransport_norm_le R.family R.makes top _ down
  intro U
  have pure:h.exponentialEntry o (R.family.localSection d) W U=0:=by
    simp [Coefficient.exponentialEntry,Coefficient.maskedTerm,x0,r0,masked,SectionData.places,SectionData.evaluate]
  have charge:=actual U
  change ‖((W.eval U:ℂ)*h.exponentialEntry o (R.family.localSection d) W U+account h W U)/(W.eval U:ℂ)‖≤C at charge
  rw [pure,mul_zero,zero_add,same] at charge
  have genuine:‖((P).eval U)⁻¹ • account h W U‖≤C:=by
    simpa only [Complex.real_smul,Complex.ofReal_inv,div_eq_inv_mul] using charge
  rw [←smul_mul_assoc,norm_mul]
  exact mul_le_mul genuine (product (a U) (b U) cap δ (gross U) (crop U) vs) (norm_nonneg _)
    ((norm_nonneg _).trans genuine)

end YM.Integration.WilsonMeasuredPublicEntranceFiredTail
end
