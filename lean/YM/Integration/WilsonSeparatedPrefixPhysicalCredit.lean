import YM.Integration.WilsonSeparatedPrefixScreenedCredit
import YM.Integration.WilsonSeparatedPrefixCohortUnscale
import YM.Integration.WilsonMovingForkMixedSeed

/-! The genuine older normalized Haar reading restores the same submitted scalar on its physical and K-born columns. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixPhysicalCredit
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Labels Source PhysicalNext.Repeat.Legato
open RG16 RG16.Literal WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingPosterior
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open private scaled from YM.Integration.WilsonSeparatedPrefixCohortUnscale
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){N per K u:ℕ}
local notation "C" => R.family
local notation "X" i:max => Config G ((C).side i per)

private theorem priced {i:ℕ}{Y:X i → ℂ}(ok:Continuous Y):funded Y:=by
  obtain ⟨a,cap⟩:=(isCompact_range ok.norm).bddAbove
  exact ⟨ok.measurable,a,fun U=>cap ⟨U,rfl⟩⟩

theorem physical (top:K≤N)(held:u≤K)(Y:X N → ℂ)(smooth:Continuous Y):
    reading R (N:=N) (credit (C) N per 0 Y K top) u held=
      actualTransport (C) (N:=N) Y (held.trans top) 1:=by
  unfold reading
  rw [cutoff R top held Y smooth,←WilsonSeparatedOriginalSlabHeldProxy.normalized R (held.trans top) Y 1]
  ring

theorem restored (top:K≤N)(held:u≤K){Y:X N→ℂ}{F:X K→ℂ}(yn:Continuous Y)(fk:Continuous F)
    (c:ℂ)(positive:c≠0){old:X N→ℂ}{trial:X K→ℂ}(oldEq:old=fun U=>c*Y U)
    (trialEq:trial=fun U=>c*F U){price:ℝ}
    (paid:‖actualTransport (C) (N:=N) old (held.trans top) 1-
      actualTransport (C) (N:=N) trial held 1‖≤price):
    ‖reading R (N:=N) (credit (C) N per 0 Y K top) u held-
      reading R (N:=N) (numerator R N per K F) u held‖≤‖c‖⁻¹*price:=by
  have thermal:reading R (N:=N) (numerator R N per K F) u held=actualTransport (C) (N:=N) F held 1:=weighted R F held
  rw [physical R top held Y yn,thermal]
  rw [oldEq,trialEq,scaled R (le_refl N) (held.trans top) Y (priced R yn) c,
    scaled R top held F (priced R fk) c,←mul_sub,norm_mul] at paid
  have cn:‖c‖≠0:=norm_ne_zero_iff.mpr positive
  calc _=‖c‖⁻¹*(‖c‖*‖actualTransport (C) (N:=N) Y (held.trans top) 1-actualTransport (C) (N:=N) F held 1‖):=by
          field_simp [cn]
       _≤_:=mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr (norm_nonneg _))

end YM.Integration.WilsonSeparatedPrefixPhysicalCredit
end
