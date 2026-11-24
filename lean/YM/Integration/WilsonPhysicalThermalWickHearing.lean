import YM.Integration.WilsonPhysicalThermalWickAnswer
import YM.Integration.WilsonPhysicalThermalWickFree
import YM.Integration.WilsonPhysicalThermalWickSpun
import YM.Integration.WilsonReporterWeightedConnected

/-! The signed connected row on two original heated Wilson fields.
The enrollment date precedes both regulators and every probe location. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickHearing
open Lattice Wilson RG Labels Function Filter
open Next.Rank Next.Rank.Atlas Next.Rank.Station Next.Rank.Perch Next.Rank.Glimmer
open Next.Rank.Configuration Next.Rank.Tapes Next.Rank.Tapes.West Next.Rank.Ribbon
open Marker Glyph Exponential Cells
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
open scoped BigOperators Classical Topology
variable {G:Gauge}{C:Family G}{d θ:ℕ}{d0:Fin 2→ℕ}
local notation "A"=>C.path.levels

theorem original (simple:G.Simple)(v:(i:Fin 2)→C.label (d0 i))(hY:∀i,d0 i≤d)
    (q:Fin 2→ℕ)(ranks:∀i,pure (q i) (thawKey (labels v hY i)))(order:∀i,q i≤d)(rise:q 0≤q 1)
    (shelf:100*(d+1)≤θ)(B:ℝ):∀ᶠ k:ℕ in atTop,
    ∀{N p:ℕ}{ξ:Purse}{P:(i:ℕ)→Rep G (C.side i p)}{x:Points 2}{Ψ:AtlasData G C.S p},
      k≤N → ξ.taylor=θ →
      ∀(fit:FitSky A ξ.band k x)(F:(i:Fin 2)→StampDuty C k N p (d0 i) ξ.taylor (P k) ξ.era.coast.Q Ψ),
      BalconSky ξ.band hY v x k ξ.taylor → BellSky A Ψ d ξ.taylor fit →
      invariantAt (C:=C) k (wood A k) p Ψ →
      (∀i,saves C (d0 i)+(q 1-q 0:ℕ)+3≤ξ.band) →
      ‖Read.maxProfile C (tested A ξ.band k x) (jointX v)‖≤B →
      ∀u:(i:Fin 2)→C.label (d0 i),(∀i,Price.Solves C (mag A ξ.band k) (d0 i) k N p (F i).T (v i) (u i)) →
      let a:=WilsonPhysicalThermalWickStretched.rates ((bill 1 (clim A k))^(q 1-q 0))
      WilsonReporterWeightedReturn.Signed (WilsonReporterWeightedOrdinary.stretch C a v)
        (WilsonReporterWeightedOrdinary.stretch C a u) fit F:=by
  have assigned:=(hat_rate A simple).eventually (WilsonPhysicalThermalWickCalendar.original (labels v hY)
    (q 1-q 0:ℕ) (Nat.cast_nonneg _) shelf)
  filter_upwards [assigned,WilsonReporterWeightedConnected.original (C:=C) (n:=2) simple B] with
    k cash log N p ξ P x Ψ hN time fit F filed bell inv fees cap u solved
  let a:=WilsonPhysicalThermalWickStretched.rates ((bill 1 (clim A k))^(q 1-q 0))
  apply log fit F (WilsonReporterWeightedOrdinary.stretch C a v) (WilsonReporterWeightedOrdinary.stretch C a u)
  · rw [WilsonPhysicalThermalWickFree.original _ (Ship.fittingSky fit) v hY q ranks]
    exact cap
  · intro y hy S
    rw [WilsonPhysicalThermalWickSpun.original _ _ _ _ _ inv]
    exact WilsonPhysicalThermalWickAnswer.original v hY fit ξ.taylor bell hN (fun i=>(F i).lights) y hy
      (filed.pends fit) filed.passes u solved q ranks order rise fees (time.symm ▸ cash) S

end YM.Integration.WilsonPhysicalThermalWickHearing
end
