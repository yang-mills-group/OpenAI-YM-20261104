import YM.Integration.WilsonOriginalTwoFlatRoseIdentity
import YM.Integration.WilsonOriginalMicroscopicEntranceTwoExits
import YM.Integration.WilsonSeparatedOriginalSlabHeldProxy
import YM.Integration.WilsonThermometerUnitFilingPosterior

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseUpper
open Finset Function Marker Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open RG16.Literal Trace.Physical.GermGraph Planned.GuardedAtom PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.Germ PhysicalNext PhysicalNext.Repeat
open WilsonOriginalMicroscopicEntranceEarlier (face)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonOriginalMicroscopicGuardedTrial (raw)
open WilsonOriginalMicroscopicEntranceFiling (units supplied)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerUnitFilingCoarse (reading)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per f n u:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j per)

/-- The entrance is a difference of ordinary conditionals on the one original law. -/
theorem law {K:ℕ}(uk:u≤K)(kn:K≤N)(Y:Cut C N per)(cont:Continuous Y)(M:(j:ℕ) → X j → ℂ):
    WilsonOriginalTwoFlatRoseIdentity.entry R uk kn Y M=
      actualTransport C (N:=N) Y (uk.trans kn) 1-actualTransport C (N:=N) (M K) uk 1:=by
  unfold WilsonOriginalTwoFlatRoseIdentity.entry
  rw [show numerator R N per K (M K)=(fun U:X K=>(((C).path.rep N per K).eval U:ℂ)*M K U) from rfl,
    WilsonThermometerUnitFilingPosterior.weighted]
  congr 1
  unfold reading
  rw [WilsonThermometerUnitFilingCoarse.cutoff R kn uk Y cont,
    ←WilsonSeparatedOriginalSlabHeldProxy.normalized R (uk.trans kn) Y]
  ring

/-- The restored face is exactly the one issued by the full original microscopic entrance.
Its incoming unit, all mixed subfaces and each selected physical dose are retained. -/
theorem original (d:Fin 3 → ℕ)(live:f+n≤N)(Y:∀i:Fin 3,(C).label (d i))
    (o:Fin 3 → Site ((C).side f per))(v:∀i:Fin 3,(C).label (d i))
    (s:(J).Mode)(uf:u≤f)(M:(j:ℕ) → X j → ℂ)
    (atK:M (f+n)=(fun U:X (f+n)=>units R d (f+n) s*face (raw R d N per (f+n)
      (pin R (Nat.le_add_right f n) o) v) s U)):
    WilsonOriginalTwoFlatRoseIdentity.entry R (uf.trans (Nat.le_add_right f n)) live
        (fun U:X N=>∏i∈s.val,(C).O N per (Y i) (pin R ((Nat.le_add_right f n).trans live) o i) U) M=
      WilsonOriginalMicroscopicEntranceTwoExits.originalRead R d live Y o v s uf 1:=by
  let kf:=Nat.le_add_right f n
  let atN:=pin R (kf.trans live) o
  let atTrial:=raw R d N per (f+n) (pin R kf o) v
  let pay:=fun i=>(supplied R d (N:=N) (pin R kf o) v i).2
  have cont:Continuous (fun U:X N=>∏i∈s.val,(C).O N per (Y i) (atN i) U):=
    continuous_finsetProd _ fun i _=>(C).continuousO N per (d i) (Y i) (atN i)
  rw [law R (uf.trans kf) live _ cont M,atK]
  exact (WilsonOriginalMicroscopicEntranceFiling.original R d Y atN live atTrial pay (uf.trans kf) s 1).symm

end YM.Integration.WilsonOriginalTwoFlatRoseUpper
end
