import YM.Integration.WilsonOriginalPublicNodalNodes
import YM.Integration.WilsonSeparatedPrefixFiledUpper

/-! The independently filed heterogeneous stations, after refunding the common
physical dose, on the original source sites and any separate inversion tree. -/
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 950000
namespace YM.Integration.WilsonOriginalPublicNodalSeed
open Finset Lattice Wilson RG Source Labels MeasureTheory PhysicalNext.Repeat.Legato
open Pert.Asymptotics RegulatorIR.FVAAlt2 XSpace XSpace.Cirrus XSpace.Normalize XSpace.Rose
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses units product)
open WilsonMovingForkSeededPoint (seats)
open WilsonOriginalPublicPivotReflected (board evaluated)
open WilsonOriginalPublicNodalEntry (dose balance)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){n:ℕ}(d:Fin n→ℕ){N per K f u:ℕ}
    (file:Filed R d K)(Y:∀i,R.family.label (d i))
local notation "g₀" => regulatorRun R.family N per K
local notation "ζ" => doses R d file.station (N:=N) (per:=per) (file.A N per) Y
local notation "α" => WilsonReflectedPublicTrialRoster.factor R K d (fun _=>1)
local notation "fire" => WilsonOriginalAlternativeFiniteSource.fired (V:=Fin n)
local notation "all" => Stock.final (Fin n)
local notation "read" => actualTransport R.family (N:=N) (p:=per)

def vector (i:Fin n):R.family.label (d i):=
  WilsonPositionProgramReportedField.entire R (d i) K (N,per) (units R d K ζ i)

/-- Each measured vector has the actual station inverse and physical length
of the deterministic K cutoff; the original gauge coupling occurs in entire. -/
theorem registered:
    dose R d (N:=N) (K:=K) (per:=per) ζ α fire=vector R d (N:=N) (per:=per) file Y:=by
  funext i
  simp only [dose,vector,units,WilsonAddressedFiniteGuardTrial.submitted,
    WilsonReflectedPublicTrialRoster.factor,WilsonOriginalAlternativeFiniteSource.fired,one_mul]

variable (fk:f≤K)(kn:K≤N)(uk:u≤K)(site:Fin n→ Cover)(point:Sample n)
    (placed:∀i,wrap (R.family.side K per) (point.layout i)=seats (R:=R) fk per site i)
local notation "pin" => seats (R:=R) fk per site
local notation "N₀" => word R d f N per (fk.trans kn) site Y
local notation "K₀" => product R d (N:=N) pin ζ
local notation "chart" => vector R d (N:=N) (per:=per) file Y

def signed (q:ℕ):ℂ:=balance R d (N:=N) (per:=per) ζ α fire all
  point.layout point.F.p (W.tree point.F.p) q uk 1

include kn placed in
theorem field (q:ℕ):
    read K₀ uk 1-evaluated q g₀ (board R W d chart point univ)=
      signed R W d (N:=N) (per:=per) file Y uk point q:=by
  have paid:=WilsonOriginalPublicNodalEntry.returned R d pin ζ α fire all point.layout
    (fun a=>placed a) point.F.p (W.tree point.F.p) q kn uk 1
  have same:WilsonAddressedFiniteGuardTrial.printed R d (N:=N) pin ζ α fire all=K₀:=by
    simpa only [Finset.prod_const_one,one_mul] using
      WilsonSeparatedPrefixChargedSeed.printed R d kn pin ζ (fun _=>1)
  rw [same] at paid
  unfold WilsonOriginalPublicPivotReflected.board
  rw [←registered R d (N:=N) (per:=per) file Y]
  exact paid

include placed in
theorem original (q:ℕ){wage:ℝ}
    (receipt:‖reading R (N:=N) (RG16.Literal.credit R.family N per 0 N₀ K kn) u uk-
      reading R (N:=N) (numerator R N per K K₀) u uk‖≤wage):
    let phase:=WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans kn) N₀
    let P:=evaluated q g₀ (board R W d chart point univ)
    let E:=signed R W d (N:=N) (per:=per) file Y uk point q
    R.family.omega N per N₀-P-E=phase+(read N₀ (uk.trans kn) 1-read K₀ uk 1) ∧
      ‖R.family.omega N per N₀-P-E‖≤‖phase‖+wage:=by
  intro phase P E
  have paid:‖read N₀ (uk.trans kn) 1-read K₀ uk 1‖≤wage:=by
    have pull:reading R (N:=N) (numerator R N per K K₀) u uk=read K₀ uk 1:=
      WilsonThermometerUnitFilingPosterior.weighted R K₀ uk
    rwa [WilsonSeparatedPrefixPhysicalCredit.physical R kn uk N₀
      (WilsonSeparatedPrefixScreenedWord.funded R d (fk.trans kn) site Y),
      pull] at receipt
  have stamped:=field R W d (N:=N) (per:=per) file Y fk kn uk site point placed q
  have step:R.family.omega N per N₀-P-E=phase+(read N₀ (uk.trans kn) 1-read K₀ uk 1):=by
    dsimp only [E,P,phase]
    rw [←WilsonOriginalPublicNodalHearing.phase R (uk.trans kn) N₀,←stamped]
    ring
  exact ⟨step,step ▸ (norm_add_le ..).trans (add_le_add le_rfl paid)⟩

/-- The registered dose-refunded receipt is also an entrance for the entire
signed nodal panel, with its physical site and measured coordinates intact. -/
theorem coissued {wage:ℝ}
    (receipt:‖reading R (N:=N) (RG16.Literal.credit R.family N per 0 N₀ K kn) u uk-
      reading R (N:=N) (numerator R N per K K₀) u uk‖≤wage):
    WilsonOriginalPublicNodalEntry.Issued R d pin ζ α fire all kn uk N₀ wage:=by
  have same:WilsonAddressedFiniteGuardTrial.printed R d (N:=N) pin ζ α fire all=K₀:=by
    simpa only [Finset.prod_const_one,one_mul] using
      WilsonSeparatedPrefixChargedSeed.printed R d kn pin ζ (fun _=>1)
  have smooth:=WilsonSeparatedPrefixScreenedWord.funded R d (fk.trans kn) site Y (p:=per)
  have bounded:WilsonOriginalMicroscopicEntranceDeposits.funded N₀:=by
    obtain ⟨m,cap⟩:=(isCompact_range smooth.norm).bddAbove
    exact ⟨smooth.measurable,m,fun U=>cap ⟨U,rfl⟩⟩
  have inside:=ActualWilsonAbsoluteTransport.weighted R.family R.makes kn
    (Envelope.compactC (WilsonSeparatedPrefixFiledUpper.continuous R d (N:=N) ζ pin))
  have receipt₀:=WilsonMeasuredPublicEntranceHeldDifference.withdraw (N:=N) R (le_refl N)
    kn uk N₀ K₀ bounded (by simpa only [Complex.real_smul] using inside) 1
  have returned:WilsonOriginalPublicNodalEntry.enter R d pin ζ α fire all kn uk N₀=
      read N₀ (uk.trans kn) 1-read (WilsonAddressedFiniteGuardTrial.printed R d (N:=N) pin ζ α fire all) uk 1:=by
    unfold WilsonOriginalPublicNodalEntry.enter
    rw [same]
    exact receipt₀
  refine WilsonOriginalPublicNodalEntry.issued R d pin ζ α fire all kn uk N₀ returned ?_
  rw [returned,same]
  have pull:reading R (N:=N) (numerator R N per K K₀) u uk=read K₀ uk 1:=
    WilsonThermometerUnitFilingPosterior.weighted R K₀ uk
  rwa [WilsonSeparatedPrefixPhysicalCredit.physical R kn uk N₀ smooth,pull] at receipt

end YM.Integration.WilsonOriginalPublicNodalSeed
end
