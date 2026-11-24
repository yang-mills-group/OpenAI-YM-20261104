import YM.Integration.WilsonOriginalCensusCanonicalTopBoard
import YM.Integration.WilsonOriginalCopiedContraction

/-! The first canonical source on the actual copied pages and its returned lower model. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalTopCopies
open Filter Function Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn
open Comparison.RG02 AllOrder AllOrder.Floe PhysicalNext.Repeat.Legato FVA1Physical.TwoReset
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic WilsonThermometerDeclaredSeeds
open WilsonOriginalCensusCanonicalRows (row)
open WilsonOriginalMixedBlockRows (room)
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open Precision Tree Exterior Bloch Pressure Push
open AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series Further.PhysicalPeriodLimitF933 Macrame
open WilsonOriginalCopiedContraction WilsonOlderFreshGraphSlate
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V](R:Run G){N i per:ℕ}(hi:i<N){h:V→ℕ}
  (d:V→ℕ)(pt:V→Chamber)(q:(j:V)→Choice R d j)(hd:∀j,0 < d j)
  (o:V→Site (R.family.side (i+1) per))(σ:ℝ)(x:Affinity.Wallet (room V))
  (grid:Side)(tiles:(R.family.side i per).val∣grid.val)
  (trees:∀u:Covers R.family.path.levels.S i grid,Forest (step R i u.val).ratio)
  (tags:∀u:Covers R.family.path.levels.S i grid,(step R i u.val).Choices)
local notation "J" => Stock.census V
local notation "M" => WilsonOriginalCensusCanonicalRows.row R d q hd o σ

def origins (b:Covers R.family.path.levels.S i grid)
    (p:Fin (Pages (R.family.side (i+1) per) (fine R i b.val)))(v:V):Lattice.Cover:=
  lift (FVA1Physical.TwoReset.copy (tiled R tiles b) ((M) v) p).center

def page (order:ℕ)(v:Stationary.Link G grid)(a:ℕ)(b:Covers R.family.path.levels.S i grid):Poly (J):=
  let link:=AllOrder.Ker.convey (coverWin b.prop) v
  let angular:=Stationary.arm G _ 1 link
  let means:=WilsonOriginalCensusCanonicalMoments.moments (h:=h)
    R d pt q N i b.val (trees b) x (origins R d q hd o σ grid tiles b) angular order
  (((Pages grid (R.family.side i b.val):ℕ):ℝ)⁻¹:ℝ) • Order.observe (J) order (Extra.Trajectories.connected means) a

variable {p':Passport (R.family.side (i+1) per) V}{μ:Type}
  (high:μ→Row p' (Stock.census V) G (Affinity.Wallet (room V)))
  (placed:p'=Passport.point o)(names:μ=V)(ink:HEq high (WilsonOriginalCensusCanonicalRows.row R d q hd o σ))
  {w:V→ℝ}{θ C:ℝ}{order seats shelf:ℕ}
  (stock:Scene.Armada high w d θ C order seats shelf)(width:0<θ)
  {m e:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
  (legal:Legal (Step.tape (e+2)) (π (i+1)))(course:Read R N m e quiet π Γ)(live : m ≤ i){τ cash:ℝ}
  (funded:Issued R N (i+1) e (quiet (i+1)) τ cash)(simple:G.Simple)(grade:order≤e+2)
local notation "color" => (fun u:Covers R.family.path.levels.S i grid=>copyColor (tiled R tiles u) high
  d (fun l=>(high l).paint x) (π (i+1)) (Step.tape (e+2)))
include placed names ink stock width legal course live funded simple grade in
theorem exact_page (u:Covers R.family.path.levels.S i grid)(v:Stationary.Link G grid)(a:ℕ):
    WilsonOriginalCopiedContraction.contraction R hi order grid (color) trees tags v a u=
      page (h:=h) R (N:=N) d pt q hd o σ x grid tiles trees order v a u:=by
  let link:=AllOrder.Ker.convey (coverWin u.prop) v
  have got:=WilsonOriginalCensusCanonicalTopBoard.original (h:=h) R d pt q hd o σ N i u.val hi
    (trees u) (tags u) (tiled R tiles u) x (π (i+1)) (Step.tape (e+2))
    (origins R d q hd o σ grid tiles u) (fun p j=>wrap_lift _) high placed names ink
    stock width legal course live funded simple link order grade
  exact congrArg (fun t=>(((Pages grid (R.family.side i u.val):ℕ):ℝ)⁻¹:ℝ) • Order.observe (J) order t a) got.2

include placed names ink stock width legal course live funded simple grade tags in
theorem published {P':Passport (R.family.side i per) V}{ν:Type}
    (next:ν→Row P' (J) G (Affinity.Wallet (room V)))
    (voted:RepresentsCover R hi (π (i+1)) (Step.tape (e+2)) order high d next)
    (v:Stationary.Link G grid)(a:ℕ)(kept:a≤order):
    Tendsto (page (h:=h) R (N:=N) d pt q hd o σ x grid tiles trees order v a)
      (coverFilter R.family.path.levels.S i grid) (𝓝 (peek tiles next d (π (i+1)) (Step.tape (e+2)) x a v)):=by
  have sold:=WilsonOriginalCopiedContraction.named (R:=R) (h:=hi) (p:=order) («M»:=high)
    (Y:=next) (published:=voted) (t:=x) (grid:=grid) (multiple:=tiles)
    (inputs:=(color)) (matched:=fun _=>rfl) (F:=trees) (tag:=tags) (A:=v) (e:=a) (he:=kept)
  apply sold.congr'
  exact Filter.Eventually.of_forall (fun u=>exact_page (h:=h) R hi d pt q hd o σ x grid tiles trees tags high
    placed names ink stock width legal course live funded simple grade u v a)

end YM.Integration.WilsonOriginalCensusCanonicalTopCopies
end
