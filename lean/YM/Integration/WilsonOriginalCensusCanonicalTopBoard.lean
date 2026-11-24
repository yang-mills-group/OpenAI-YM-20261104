import YM.Integration.WilsonOriginalCensusCanonicalMoments
import YM.Integration.WilsonOriginalCensusCanonicalGaussian

/-! The normalized ordinary and connected tables on the first finite Wilson board, at every retained age. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalTopBoard
open Function Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn
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
open scoped Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V](R:Run G)(d:V→ℕ){h:V→ℕ}(pt:V→Chamber)
  (q:(j:V)→Choice R d j)(hd:∀j,0 < d j)
  {n:Side}(o:V→Site n)(σ:ℝ)(N i per:ℕ)(hi:i<N)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(copying:n.val∣(fine R i per).val)
  (x:Affinity.Wallet (room V))(L:Layout G)(tape:Finset Age)
local notation "M" => row R d q hd o σ
local notation "J" => Stock.census V
local notation "K" => model R N i per hi
variable (addresses:Fin (Pages n (fine R i per)) → V → Lattice.Cover)
  (located:∀p j,wrap (fine R i per) (addresses p j)=(FVA1Physical.TwoReset.copy copying (row R d q hd o σ j) p).center)

include located in
theorem original {p':Passport n V}{μ:Type}
    (high:μ→Row p' (J) G (Affinity.Wallet (room V)))(placed:p'=Passport.point o)(names:μ=V)(ink:HEq high (M))
    {w:V→ℝ}{width fare:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada high w d width fare order seats shelf)(width0:0<width)(legal:Legal tape L)
    {m e:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e quiet π Γ)(lo:m ≤ i){τ cash:ℝ}
    (funded:Issued R N (i+1) e (quiet (i+1)) τ cash)(simple:G.Simple)
    (b:Stationary.Link G (coarse R i per))(r:ℕ)(grade:r ≤ e+2):
    let angular:=Stationary.arm G _ 1 b
    let filed:=Bulk.Fk (K) F tag (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2))
      (copyColor copying high d (fun j=>(high j).paint x) L tape)) angular r
    let full:=WilsonOriginalCensusCanonicalMoments.moments (h:=h) (n:=n) R d pt q N i per F x addresses angular r
    Order.ratio filed=full ∧ Order.logMarked filed=Extra.Trajectories.connected full:=by
  intro angular filed full
  subst p'
  subst μ
  cases eq_of_heq ink
  have received:=WilsonOriginalCensusCanonicalGaussian.original (h:=h) R d pt q hd o σ N i per hi F tag
    copying x L tape addresses located stock width0 legal course lo funded b r grade
  have rewritten:=WilsonOriginalCensusCanonicalWick.original (h:=h) (n:=n) R d pt q N i per hi F tag x addresses angular r
  have normalized:=WilsonOriginalCensusCanonicalMoments.original (h:=h) (n:=n)
    R d pt q N i per hi F tag x addresses simple angular r
  have same:Order.ratio filed=full:=received.1.trans ((congrArg Order.ratio rewritten).trans normalized)
  exact ⟨same,congrArg Extra.Trajectories.connected same⟩

end YM.Integration.WilsonOriginalCensusCanonicalTopBoard
end
