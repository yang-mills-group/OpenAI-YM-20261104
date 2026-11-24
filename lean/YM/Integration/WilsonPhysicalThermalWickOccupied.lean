import YM.Integration.WilsonPhysicalThermalWickCalendar
import YM.Integration.WilsonPhysicalThermalWickSky
import YM.Integration.WilsonPhysicalThermalWickFaces
import YM.Integration.WilsonPhysicalThermalWickDegree

/-! The rank difference is earned on the submitted original two-location
Wilson ordinary row, including its off-calibrated high dates and exact
conditional mean, at each actual earlier held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickOccupied
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
    (S:modes (Fin 2))(high:1∈S.val):
    (bill 1 s)^(q 1-q 0)*‖(Answer Y (choose A b k x) (beforeSky A b k) (fun i=>Z i (u i)) (fun U=>(m U:ℂ))).part S-
      (Read.maxProfile C (tested A b k x) (jointX v)).part S‖≤bill (-127/128) s:=by
  let F:=labels v hY
  let w:=choose A b k x
  let I:trimV (lengthW s) G→Address G:=Subtype.val
  let Γ:=Γre C.path.levels.S Y w (beforeSky A b k)
  let μ:=μre C.path.levels.S Y w (beforeSky A b k) (fun U=>(m U:ℂ))
  let Q:=primary d I (mag A b k) Γ (Γs A Y w (beforeSky A b k))
  let z:=Beamer.seen d I (mag A b k) μ
  let J:=pot S.val (fun i=>thawKey (F i))
  let middle:=blend (Particle.ferry Q) (z∘Particle.polar) J
  let above:=(Answer Y w (beforeSky A b k) (fun i=>Z i (u i)) (fun U=>(m U:ℂ))).part S
  let below:=(Read.maxProfile C (tested A b k x) (jointX v)).part S
  let P:=bill 1 s
  let a:=P^(q 1-q 0)
  let err:=WilsonPhysicalThermalWickGain.error degree s
  let B:=bill (fuel degree 2) s
  let wage:=Rise.coin J*(err*priced (B+err) (2*d))
  have pos:0≤a:=pow_nonneg (Real.exp_pos _).le _
  have paid:=ready S.val
  have tariff:a=bill ((q 1-q 0:ℕ):ℝ) s:=by simpa only [a,P,one_mul] using bills 1 s (q 1-q 0)
  have top:a*‖above-middle‖≤bill (-3/2) s:=by
    have posted:=WilsonPhysicalThermalWickPosted.original v hY g degree h hN ink m hm hs H u solved (q 1-q 0:ℕ) fees S
    exact (mul_le_mul_of_nonneg_left posted pos).trans (tariff.symm ▸ paid.1)
  have bottom:a*‖middle-below‖≤wage:=by
    have cover:=WilsonPhysicalThermalWickFaces.covers (costed 1 s zero_le_one) q rise S.val high
    have received:=WilsonPhysicalThermalWickSky.original v hY g degree h m hm hs q ranks S (2*d)
      (WilsonPhysicalThermalWickDegree.original q _ ranks d order S.val)
    exact (mul_le_mul_of_nonneg_right cover (norm_nonneg (middle-below))).trans received
  change a*‖above-below‖≤_
  calc
    _≤a*(‖above-middle‖+‖middle-below‖):=
      mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub above middle below) pos
    _≤bill (-3/2) s+wage:=by rw [mul_add];exact add_le_add top bottom
    _≤_:=by rw [add_comm];exact paid.2

end YM.Integration.WilsonPhysicalThermalWickOccupied
end
