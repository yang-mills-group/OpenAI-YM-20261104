import YM.MS.Arc.Pumps
import YM.MS.Arc.R1
import YM.MS.City.Lines
import YM.MS.Pearl.Flats
import YM.MS.Rock.Stone
import YM.MS.Train.MeasureD

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Filter Function Finset MeasureTheory
open Plane Koszul Flux Landau Arts Arc Wire Rock Path Alps
open Shine Hem Mell Pearl Train
open scoped Topology ContDiff Interval
variable {G: Gauge} {m: ℕ} {z: ℂ} {F H: Mob G} {V: Flats G}
variable (s: ℝ) (i j: Cfield G m) (p: SectorP m)
/-- Half the shell propagator = per d(log length). -/
def halfD (s : ℝ) : Rip G := fun _ i j p =>
  (Real.exp s : ℝ) • Landau.choir (City.L0 (Real.exp s)) id i j p
/-- An individual bridge allocation, before shuffle and before possible 1/2 for
**component order**. The Feynman rule is the *full* shell, one orientation. -/
def bridgeTerm (s : ℝ) (F H : Mob G) (u v : Legs (Shore G m)) : ℂ :=
  let q := - net u
  ∑ i : Cfield G m, ∑ j : Cfield G m,
    2 * halfD s m i j q *
      (cross (Landau.parity j) (degree (field Landau.parity) u) * F m ((i,q)::u)) *
      H m ((j,-q)::v)
/-- Forced-edge operation on one pair of kernels. No component-order fee here. -/
def bridging (s : ℝ) (F H : Mob G) : Mob G := fun _ w =>
  scatter (field Landau.parity) w (bridgeTerm s F H)
/-- Scale sector forced by the given bridge (shell evaluated at log length 0).
Keep pages according to actual loop-integral counts, also when a child includes
a pole page (one does not count the loops used to *calculate* that local CT). -/
def bridgeForce (V W : Flats G) : Flats G :=
  V.sum fun i f => W.sum fun j g => Finsupp.single (j+i) (fun z => bridging 0 (f z) (g z))
/-- Ordered cycle rule with both integral signs (inner, over the plane, in `carpet`). -/
def radialClose (U : Rip G) (z : ℂ) (y : ℝ) (F : Mob G) : Mob G :=
  fun m w =>
    tenorK z y * (
    gage m • ∫ t in Set.Ioi (0:ℝ),
      ((t:ℂ)^(2*z+1)) * pruning (m+1) (carpet (Px m) (wing z U F (ray w))) (t, (1:ℝ)))
/-- Shell closing a further pair inside one connected diagram (at log length 0),
over all ordered end assignments, incrementing loop count. -/
def closeForce (V : Flats G) : Flats G := V.sum fun i f =>
  Finsupp.single (i+1) (fun z => radialClose (halfD 0) z 0 (f z))
end YM.MS.Graphical
