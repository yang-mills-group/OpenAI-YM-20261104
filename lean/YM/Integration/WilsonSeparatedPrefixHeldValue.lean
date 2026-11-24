import YM.Integration.WilsonSeparatedPrefixOrientedValue
import YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution

/-! Normalize the actual cutoff and the independently planted word at the same held field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixHeldValue
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Labels Source PhysicalNext.Repeat.Legato
open RG16 RG16.Literal WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingPosterior
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open private priced from YM.Integration.WilsonSeparatedPrefixPhysicalCredit
open private scaled from YM.Integration.WilsonSeparatedPrefixCohortUnscale
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){N per K u:ℕ}
local notation "C" => R.family
local notation "X" i:max => Config G ((C).side i per)

theorem physical (W:X u)(top:K≤N)(held:u≤K)(Y:X N → ℂ)(smooth:Continuous Y):
    readingAt R (N:=N) (credit (C) N per 0 Y K top) held W=
      actualTransport (C) (N:=N) Y (held.trans top) W:=by
  unfold readingAt
  rw [cutoff R top held Y smooth,←WilsonSeparatedOriginalSlabHeldProxy.normalized R (held.trans top) Y W]
  ring

theorem restored (W:X u)(top:K≤N)(held:u≤K){Y:X N→ℂ}{F:X K→ℂ}(yn:Continuous Y)(fk:Continuous F)
    (c:ℂ)(positive:c≠0){old:X N→ℂ}{trial:X K→ℂ}(oldEq:old=fun U=>c*Y U)
    (trialEq:trial=fun U=>c*F U){price:ℝ}
    (paid:‖actualTransport (C) (N:=N) old (held.trans top) W-
      actualTransport (C) (N:=N) trial held W‖≤price):
    ‖readingAt R (N:=N) (credit (C) N per 0 Y K top) held W-
      readingAt R (N:=N) (numerator R N per K F) held W‖≤‖c‖⁻¹*price:=by
  have thermal:readingAt R (N:=N) (numerator R N per K F) held W=actualTransport (C) (N:=N) F held W:=by
    unfold readingAt actualTransport numerator
    simp only [Complex.real_smul,Complex.ofReal_inv]
  rw [physical R W top held Y yn,thermal]
  rw [oldEq,trialEq,scaled R (le_refl N) (held.trans top) Y (priced R yn) c,
    scaled R top held F (priced R fk) c,←mul_sub,norm_mul] at paid
  have cn:‖c‖≠0:=norm_ne_zero_iff.mpr positive
  calc _=‖c‖⁻¹*(‖c‖*‖actualTransport (C) (N:=N) Y (held.trans top) W-actualTransport (C) (N:=N) F held W‖):=by
          field_simp [cn]
       _≤_:=mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr (norm_nonneg _))

end YM.Integration.WilsonSeparatedPrefixHeldValue
namespace YM.Integration.WilsonSeparatedPrefixHeldValue
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonSeparatedPrefixOrientedValue (originalWord)
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open WilsonMovingForkMixedSeed
open WilsonMovingForkSeededPoint (seats)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){f N per K u:ℕ}
local notation "C" => R.family

theorem original (file:Filed R d K)(live:K≤N)(fk:f≤K)(held:u≤K)(W:Config G ((C).side u per))(site:Fin n→ Cover)
    (Y:∀i,(C).label (d i))(τ:Fin n→Motion)(c:Fin n→ℂ)(positive:∀i,c i≠0):
    let w:=fun a=>Motion.patch ((C).labels.level (d a)) (τ a)
      (doses R d file.station (N:=N) (per:=per) (file.A N per) Y a)
    let ξ:=seats (R:=R) fk per site
    let incumbent:=originalWord R d (f:=f) (N:=N) (per:=per) site Y τ c
    let planted:=WilsonAddressedFiniteGuardTrial.printed R d (N:=N) ξ w
      (WilsonReflectedPublicTrialRoster.factor R K d c) WilsonOriginalAlternativeFiniteSource.fired (Stock.final (Fin n))
    let actual:=word R d f N per (fk.trans live) site (fun a=>displayed R (d a) (Y a) (τ a))
    ∀(read:ℂ)(bill:ℝ),
    read=actualTransport (C) (N:=N) incumbent (held.trans live) W-actualTransport (C) (N:=N) planted held W ∧
    ‖read‖≤bill →
    ‖readingAt R (N:=N) (credit (C) N per 0 actual K live) held W-
      readingAt R (N:=N) (numerator R N per K (product R d (N:=N) ξ w)) held W‖≤(∏i,‖c i‖)⁻¹*bill:=by
  intro w ξ incumbent planted actual read bill earning
  have result:=restored R W live held
    (WilsonSeparatedPrefixScreenedWord.funded R (p:=per) d (fk.trans live) site (fun a=>displayed R (d a) (Y a) (τ a)))
    (WilsonSeparatedPrefixFiledUpper.continuous R d (N:=N) w ξ) (∏i,c i)
    (Finset.prod_ne_zero_iff.mpr fun i _=>positive i) (WilsonSeparatedPrefixOrientedValue.physical R d (per:=per) (fk.trans live) site Y τ c)
    (WilsonSeparatedPrefixChargedSeed.printed R d live ξ w c) (earning.1 ▸ earning.2)
  simpa only [norm_prod] using result

end YM.Integration.WilsonSeparatedPrefixHeldValue
end
