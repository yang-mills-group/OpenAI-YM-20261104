import YM.Integration.WilsonOriginalReceivedCopiedCover
import YM.Integration.WilsonOriginalCopiedHistory

/-! The model filed before the physical election determines every finite input and its copied pupil. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNamedCompactCover
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open FVA1Physical.TwoReset WilsonOriginalCopiedHistory
open scoped Classical BigOperators Topology

theorem color {G:Gauge} {V ι ν E:Type} [DecidableEq V] {n f:Side} {C:Census V}
    {a b:Passport n V} {M:ι→Row a C G E} {L:ν→Row b C G E}
    (site:a=b) (keys:ι=ν) (same:HEq M L) (div:n.val∣f.val) (grades:V→ℕ) (x:E)
    (quiet:Layout G) (tape:Finset Age) :
    copyColor div M grades (fun z=>(M z).paint x) quiet tape =
      copyColor div L grades (fun z=>(L z).paint x) quiet tape:=by
  cases site
  cases keys
  have e:=eq_of_heq same
  rw [e]

variable {G:Gauge} (R:Run G) {i N per:ℕ} (cut:i<N) (quiet:Layout G) (tape:Finset Age)
  {V ι E:Type} [DecidableEq V] [Fintype V] {C:Census V} (o:Passport (R.family.side (i+1) per) V)
  (M:ι→Row o C G E) (grades:V→ℕ) (order:ℕ)

def declared (x:E) : Values G C (R.family.side i per):=
  block R cut order (fun _ div=>copyColor div M grades (fun z=>(M z).paint x) quiet tape)

theorem paid {ν μ:Type} {o':Passport (R.family.side (i+1) per) V} {b:Passport (R.family.side i per) V}
    (issued:ν→Row o' C G E) (Y:μ→Row b C G E) (site:o'=o) (keys:ν=ι)
    (same:HEq issued M) (actual:RepresentsCover R cut quiet tape order issued grades Y)
    (x:E) (grid:Side) (div:(R.family.side i per).val∣grid.val) (d:ℕ) (hd:d ≤ order)
    (A:Stationary.Link G grid) :
    declared R cut quiet tape o M grades order x grid div d A=peek div Y grades quiet tape x d A:=by
  apply WilsonOriginalCoverCoefficient.identified
  let input:=fun c:Covers R.family.path.levels.S i grid=>copyColor (tiled R div c) M grades (fun z=>(M z).paint x) quiet tape
  exact WilsonOriginalCopiedContraction.named (R:=R) (h:=cut) (p:=order) (M:=issued) (Y:=Y)
    (published:=actual) (t:=x) (grid:=grid) (multiple:=div) (inputs:=input)
    (matched:=fun c=>color site keys same (tiled R div c) grades x quiet tape)
    (F:=WilsonOriginalCopiedHistory.forest R i grid) (tag:=WilsonOriginalCopiedHistory.tag R i grid)
    (A:=A) (e:=d) (he:=hd)

end YM.Integration.WilsonOriginalNamedCompactCover
