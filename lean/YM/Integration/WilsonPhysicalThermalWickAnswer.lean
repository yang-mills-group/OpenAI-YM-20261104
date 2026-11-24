import YM.Integration.WilsonPhysicalThermalWickOccupied
import YM.Integration.WilsonPhysicalThermalWickStretched

/-! All original Wilson ordinary faces on the two fitted heat sources, after the actual higher-rank input is enlarged on its original chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickAnswer
open Lattice Wilson RG Labels Function Filter
open Next.Rank Next.Rank.Atlas Next.Rank.Station Next.Rank.Perch Next.Rank.Glimmer
open Next.Rank.Prayer Next.Rank.Beamer Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal
open Marker Glyph Exponential Cells
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
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
    (q:Fin 2→ℕ)(ranks:∀i,pure (q i) (thawKey (labels v hY i)))(order:∀i,q i≤d)(rise:q 0≤q 1)
    (fees:∀i,saves C (d0 i)+(q 1-q 0:ℕ)+3≤b)
    (ready:WilsonPhysicalThermalWickCalendar.Bought (labels v hY) (q 1-q 0:ℕ) s degree)
    (S:modes (Fin 2)):
    let a:=WilsonPhysicalThermalWickStretched.rates ((bill 1 s)^(q 1-q 0))
    ‖(Answer Y (choose A b k x) (beforeSky A b k) (fun i=>Z i (WilsonReporterWeightedOrdinary.stretch C a u i))
      (fun U=>(m U:ℂ))).part S-(Read.maxProfile C (tested A b k x)
        (jointX (WilsonReporterWeightedOrdinary.stretch C a v))).part S‖≤bill (-63/64) s:=by
  dsimp only
  rw [WilsonPhysicalThermalWickStretched.booked,WilsonPhysicalThermalWickStretched.charge,←mul_sub,
    WilsonPhysicalThermalWickStretched.mask]
  by_cases hi:1∈S.val
  · rw [if_pos hi,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (show 0≤bill 1 s from (Real.exp_pos _).le) _)]
    exact (WilsonPhysicalThermalWickOccupied.original v hY g degree h hN ink m hm hs H u solved q ranks order rise
      fees ready S hi).trans (billed s (by norm_num))
  · rw [if_neg hi,one_mul]
    exact (Atlas.sizesXSky v g degree hY hN ink h m hm H u solved hs S).trans (billed s (by norm_num))

end YM.Integration.WilsonPhysicalThermalWickAnswer
end
