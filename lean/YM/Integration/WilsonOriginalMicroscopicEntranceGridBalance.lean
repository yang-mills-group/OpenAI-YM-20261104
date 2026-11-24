import YM.Integration.WilsonOriginalMicroscopicEntranceGridStock
import YM.Integration.WilsonOriginalMicroscopicEntranceHalo
import YM.Integration.WilsonOriginalMicroscopicGuardedGridSchool

/-! The original physical upper entrance, read at an arbitrary earlier held field,
with all three pre-elected fits and the actual guard repair. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceGridBalance
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics
open PhysicalNext OPE.Therm Push.AbsoluteSums.Animals Next.Foundations Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap RG05Readout RG05Readout.Address
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedNomination WilsonOriginalMicroscopicGuardedReporters
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open WilsonOriginalMicroscopicGuardedPage
open WilsonOriginalMicroscopicGuardedPageSchool WilsonAddressedRestartedColumn
open WilsonPositionProgramOriginalBlockedTrial RG05Readout.Records
open scoped Classical Topology BigOperators
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiledPress OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonOriginalMicroscopicEntranceGridStock (account Filed)
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceSockets (read)
open WilsonOriginalMicroscopicGuardedTrial (raw guarded gap)
open WilsonOriginalMicroscopicGuardedGridSchool (Placed)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(d j:Fin 3→ℕ){f n N p:ℕ}
local notation "CF" => R.family
local notation "J" => Stock.census (Fin 3)

def coord (d j:Fin 3→ℕ)(Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))
    (A:∀a:Fin 3,R.family.label (d a)≃ₗ[ℂ]R.family.label (d a))(N p:ℕ)(a:Fin 3):R.family.label (d a):=
    (A a).symm (WilsonOriginalMicroscopicGuardedPageSchool.euler R d j Y N p a)

def slotFare (d:Fin 3→ℕ)(base higher:ℕ)(v:∀a:Fin 3,R.family.label (d a))(a:Fin 3):ℝ:=
    hike R.family higher base rate*((1+4*stock R.family higher)*((R.family.labels.level (d a)).coeffSize (v a)))

variable (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))(A:∀a:Fin 3,R.family.label (d a)≃ₗ[ℂ]R.family.label (d a))
variable (live:f+n≤N)(o:Fin 3→Site (R.family.side f p))

theorem paid (placed:Placed R d j Y f n N p live A):
    ∃Z:∀a:Fin 3,store R.family (d a) p f, Filed R d (N:=N) (n:=n) (fun a=>Y a (N,p)) o
      (coord R d j Y A N p) (slotFare R d f (f+n) (coord R d j Y A N p)) Z:=by
  let Z:=fun a:Fin 3=>Classical.choose (placed a (o a))
  exact ⟨Z,fun a=>(Classical.choose_spec (placed a (o a))).1⟩

theorem original {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
    (mature:∀a,R.family.ref (d a)≤f)(placed:Placed R d j Y f n N p live A):
    let fk:f≤f+n:=Nat.le_add_right f n
    let high:=fun a=>Y a (N,p)
    let seat:=coord R d j Y A N p
    let B:=slotFare R d f (f+n) seat
    let upper:=pin R (fk.trans live) o
    let sites:=pin R fk o
    ∃Z:∀a:Fin 3,store R.family (d a) p f,
      Filed R d (N:=N) (n:=n) high o seat B Z ∧
      ∀(s:(J).Mode){u:ℕ}(earlier:u≤f)(W:Config G (R.family.side u p)),
      let posted:=actualTransport R.family (N:=N) (account R d live high o seat Z s) earlier W
      read R d high upper live (earlier.trans fk) (guarded R d N p (f+n) sites seat) s W=posted ∧
      read R d high upper live (earlier.trans fk) (raw R d N p (f+n) sites seat) s W=
        posted-units R d (f+n) s*actualTransport R.family (N:=N) (gap R d N p (f+n) sites seat s.val) (earlier.trans fk) W:=by
  intro fk high seat B upper sites
  obtain ⟨Z,stamp⟩:=paid R d j Y A live o placed
  refine ⟨Z,stamp,?_⟩
  intro s u earlier W posted
  have first:=WilsonOriginalMicroscopicEntranceGridStock.original R d live high o seat B Z mature stamp s earlier W
  have delta:=WilsonOriginalMicroscopicEntranceSockets.correction R d κ pt high upper sites seat live (earlier.trans fk) s W
  change read R d high upper live (earlier.trans fk) (guarded R d N p (f+n) sites seat) s W=posted at first
  rw [first] at delta
  exact ⟨first,by linear_combination delta⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceGridBalance
end
