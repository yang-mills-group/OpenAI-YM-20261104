import YM.Integration.WilsonPhysicalThermalWickSubmitted
import YM.Integration.WilsonPhysicalThermalWickBooking
import YM.TraceExtension.Prom.Front.West.Mooncake

/-! The actual untrimmed posted Wilson group, at every cutoff and period.
Both the Schur correction and the earned variation on the clipped source
stay on their original sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickPosted
open Lattice Wilson RG Labels Function Filter
open Next.Rank Next.Rank.Atlas Next.Rank.Station Next.Rank.Perch Next.Rank.Glimmer
open Next.Rank.Prayer Next.Rank.Beamer Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal
open Marker Glyph Exponential Cells
open scoped BigOperators Classical Topology
variable {G:Gauge}{C:Family G}{d k N p:ℕ}{x:Points 2}{b:ℝ}{Y:AtlasData G C.S p}
    {d0:Fin 2→ℕ}(v:(i:Fin 2)→C.label (d0 i))(hY:∀i,d0 i≤d)(g:FitSky C.path.levels b k x)
    (degree:ℕ)(h:BellSky C.path.levels Y d degree g)
local notation "A"=>C.path.levels
local notation "s"=>clim A k
variable {Z:(i:Fin 2)→Heater C k (d0 i)}{T:(i:Fin 2)→Module.End ℂ (C.label (d0 i))}

include h in
theorem original (hN:k≤N)(ink:∀i,Heating C k N p (d0 i) degree (Z i) (T i))
    (m:Chamber G C.S (middleSky A b k) p→ℝ)(hm:Wind A m (fraction 2 degree s))
    (hs:Meridian (G:=G) d (Ship.fittingSky g) (fraction 2 degree s) (fraction 2 degree s) (bill (-3) s)
      (bill (fuel degree 2) s) (bill (-2) s) (mag A b k) (lengthW s))
    (H:passingX hY v k degree b)(u:(i:Fin 2)→C.label (d0 i))
    (solved:∀i,Price.Solves C (mag A b k) (d0 i) k N p (T i) (v i) (u i))
    (L:ℝ)(fees:∀i,saves C (d0 i)+L+3≤b)(mode:modes (Fin 2)):
    let w:=choose A b k x
    let I:trimV (lengthW s) G→Address G:=Subtype.val
    let r:=mag A b k
    let Γ:=Γre C.path.levels.S Y w (beforeSky A b k)
    let μ:=μre C.path.levels.S Y w (beforeSky A b k) (fun U=>(m U:ℂ))
    let Q:=primary d I r Γ (Γs A Y w (beforeSky A b k))
    let z:=Beamer.seen d I r μ
    let F:=fun i=>raiseLabel G (hY i) ((C.labels.level (d0 i)).coords.symm (v i))
    let J:=pot mode.val (fun i=>thawKey (F i))
    let B:=bill (fuel degree 2) s
    let ξ:=bill (-L-2) s
    ‖(Answer Y w (beforeSky A b k) (fun i=>Z i (u i)) (fun U=>(m U:ℂ))).part mode-
      blend (Particle.ferry Q) (z∘Particle.polar) J‖≤
       mode.val.card*ξ*(WilsonPhysicalThermalWickSurplus.cost F+ξ)^mode.val.card*priced B (2*degree):=by
  intro w I r Γ μ Q z F J B ξ
  let M:=fun _:Fin 2=>features d I r
  let P:=fun i=>Z i (u i)
  obtain ⟨Y₀,baseBought,xiBought,bought,retained⟩:=
    WilsonPhysicalThermalWickBooking.original v hY hN ink H u solved L fees
  have sell:Sorts Q z B:=(Prayer.resolution d (Ship.fittingSky g) r _ hs I (fun i=>(tracing ..).1 i.property)
    Γ μ _ (h.verdict m hm)).1
  have precut:=WilsonPhysicalThermalWickSubmitted.original (Z:=Z) g degree h u
    (zero_lt_one.trans_le retained.radius) m hm mode
  have receipt:‖blend Q z (pot mode.val (Particle.cast M P))-blend (Particle.ferry Q) (z∘Particle.polar) J‖≤
      mode.val.card*Y₀.ξ*(Y₀.base+Y₀.ξ)^mode.val.card*priced Y₀.B (2*degree):=
    WilsonPhysicalThermalWickSurplus.original retained mode.val Q z (bought.symm ▸ sell)
  rw [precut]
  simpa only [baseBought,xiBought,bought] using receipt

end YM.Integration.WilsonPhysicalThermalWickPosted
end
