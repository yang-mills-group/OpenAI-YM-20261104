import YM.Integration.WilsonSeparatedPrefixFiledUpper

/-! Keep the actual turn on the cutoff cylinder and on the charged independently held seed separately. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixOrientedValue
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonMovingForkMixedSeed
open WilsonMovingForkSeededPoint (seats)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){f N per K u:ℕ}
local notation "C" => R.family

def originalWord (site:Fin n→ Cover)(Y:∀i,(C).label (d i))(τ:Fin n→Motion)(c:Fin n→ℂ):
    Cut (C) N per:=fun U=>∏a∈(Stock.final (Fin n)).val,c a *
      (C).O N per (displayed R (d a) (Y a) (τ a)) (anchorAt R (snap (C) f per site a) N) U

theorem physical (live:f≤N)(site:Fin n→ Cover)(Y:∀i,(C).label (d i))(τ:Fin n→Motion)(c:Fin n→ℂ):
    originalWord R d (f:=f) (N:=N) (per:=per) site Y τ c=
      fun U=>(∏i,c i)*word R d f N per live site (fun a=>displayed R (d a) (Y a) (τ a)) U:=by
  funext U
  change (∏i,c i*(C).O N per _ (anchorAt R (snap (C) f per site i) N) U)=_
  simp only [Finset.prod_mul_distrib,WilsonAddressedPublicGridRooms.top R live,word]

theorem original (file:Filed R d K)(live:K≤N)(fk:f≤K)(held:u≤K)(site:Fin n→ Cover)
    (Y:∀i,(C).label (d i))(τ:Fin n→Motion)(c:Fin n→ℂ)(positive:∀i,c i≠0):
    let w:=fun a=>Motion.patch ((C).labels.level (d a)) (τ a)
      (doses R d file.station (N:=N) (per:=per) (file.A N per) Y a)
    let ξ:=seats (R:=R) fk per site
    let incumbent:=originalWord R d (f:=f) (N:=N) (per:=per) site Y τ c
    let planted:=WilsonAddressedFiniteGuardTrial.printed R d (N:=N) ξ w
      (WilsonReflectedPublicTrialRoster.factor R K d c) WilsonOriginalAlternativeFiniteSource.fired (Stock.final (Fin n))
    let actual:=word R d f N per (fk.trans live) site (fun a=>displayed R (d a) (Y a) (τ a))
    ∀(read:ℂ)(bill:ℝ),
    read=actualTransport (C) (N:=N) incumbent (held.trans live) 1-actualTransport (C) (N:=N) planted held 1 ∧
    ‖read‖≤bill →
    ‖reading R (N:=N) (credit (C) N per 0 actual K live) u held-
      reading R (N:=N) (numerator R N per K (product R d (N:=N) ξ w)) u held‖≤(∏i,‖c i‖)⁻¹*bill:=by
  intro w ξ incumbent planted actual read bill earning
  have result:=WilsonSeparatedPrefixPhysicalCredit.restored R live held
    (WilsonSeparatedPrefixScreenedWord.funded R (p:=per) d (fk.trans live) site (fun a=>displayed R (d a) (Y a) (τ a)))
    (WilsonSeparatedPrefixFiledUpper.continuous R d (N:=N) w ξ) (∏i,c i)
    (Finset.prod_ne_zero_iff.mpr fun i _=>positive i) (physical R d (per:=per) (fk.trans live) site Y τ c)
    (WilsonSeparatedPrefixChargedSeed.printed R d live ξ w c) (earning.1 ▸ earning.2)
  simpa only [norm_prod] using result

end YM.Integration.WilsonSeparatedPrefixOrientedValue
end
