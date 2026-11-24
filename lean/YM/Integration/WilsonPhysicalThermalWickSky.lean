import YM.Integration.WilsonPhysicalThermalWickReturned
import YM.Integration.WilsonPhysicalThermalWickGain
import YM.Integration.WilsonPhysicalThermalWickLabels
import YM.TraceExtension.Prom.Front.West.Mooncake

/-! Take the two raw angular measurements on the announced native Wilson sky
and on its exact Schur covariance, affine mean, and elected maximum profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickSky
open Lattice Wilson RG Labels Function Filter
open Next.Rank Next.Rank.Atlas Next.Rank.Station Next.Rank.Perch Next.Rank.Glimmer
open Next.Rank.Prayer Next.Rank.Beamer Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal
open Marker Glyph Exponential Cells
open WilsonPhysicalThermalWickRescale
open scoped BigOperators Classical Topology
variable {G:Gauge}{C:Family G}{d k N p:ℕ}{x:Points 2}{b:ℝ}{Y:AtlasData G C.S p}
    {d0:Fin 2→ℕ}(v:(i:Fin 2)→C.label (d0 i))(hY:∀i,d0 i≤d)(g:FitSky C.path.levels b k x)
    (degree:ℕ)(h:BellSky C.path.levels Y d degree g)

def labels (i:Fin 2):Label G d:=raiseLabel G (hY i) ((C.labels.level (d0 i)).coords.symm (v i))

local notation "A"=>C.path.levels
local notation "s"=>clim A k

include h in
theorem original (m:Chamber G C.S (middleSky A b k) p→ℝ)(hm:Wind A m (fraction 2 degree s))
    (hs:Meridian (G:=G) d (Ship.fittingSky g) (fraction 2 degree s) (fraction 2 degree s) (bill (-3) s)
      (bill (fuel degree 2) s) (bill (-2) s) (mag A b k) (lengthW s))
    (q:Fin 2→ℕ)(ranks:∀i,pure (q i) (thawKey (labels v hY i)))(Z:modes (Fin 2))
    (D:ℕ)(roof:(pot Z.val (fun i=>thawKey (labels v hY i))).totalDegree≤D):
    let w:=choose A b k x
    let g₀:trimV (lengthW s) G→Address G:=Subtype.val
    let Γ:=Γre C.path.levels.S Y w (beforeSky A b k)
    let μ:=μre C.path.levels.S Y w (beforeSky A b k) (fun U=>(m U:ℂ))
    let Q:=primary d g₀ (mag A b k) Γ (Γs A Y w (beforeSky A b k))
    let z:=Beamer.seen d g₀ (mag A b k) μ
    let J:=pot Z.val (fun i=>thawKey (labels v hY i))
    let E:=WilsonPhysicalThermalWickGain.error degree s
    ‖∏i∈Z.val,(WilsonPhysicalThermalWickPrice.scales (bill 1 s) i)^(q i)‖*
      ‖blend (Particle.ferry Q) (z∘Particle.polar) J-(Read.maxProfile C (tested A b k x) (jointX v)).part Z‖≤
      Rise.coin J*(E*priced (bill (fuel degree 2) s+E) D):=by
  dsimp only
  have low:(Read.maxProfile C (tested A b k x) (jointX v)).part Z=
      blend (currentX (Ship.fittingSky g) G d) 0 (pot Z.val (fun i=>thawKey (labels v hY i))):=
    (stagesX v hY _ (Ship.fittingSky g) Z).trans (Configuration.G_subset (Ship.fittingSky g) (labels v hY) Z)
  rw [low]
  exact WilsonPhysicalThermalWickReturned.original _ (costed 1 s zero_le_one) hs _ (fun i=>(tracing ..).1 i.property)
    _ _ _ (h.verdict m hm) _ q ranks Z.val D roof

end YM.Integration.WilsonPhysicalThermalWickSky
end
