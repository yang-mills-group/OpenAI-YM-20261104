import YM.Integration.WilsonReceivedCanonicalSocketGaussian
import YM.Integration.WilsonThermometerPositionFilmSelf

/-! One chosen physical side and exactly the submitted site of every raw canonical socket. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalSocketSelf
open Function Filter Finset Lattice Wilson Laurent RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Comparison.RG02.Cumulants Next.SectorChange AllOrder AllOrder.Floe
open PhysicalNext.Repeat.Legato Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical.TwoReset WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds WilsonOriginalThermometerPalette
open WilsonReceivedCanonicalSocketRows WilsonReceivedCanonicalSocketFields WilsonReceivedCanonicalSocketSeed
open Pressure Push Push.AbsoluteSums Precision Tree Exterior Bloch PowerSeries
open PhysicalForestMarkedRay FVA1Physical.TwoReset
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)

open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonReceivedCanonicalSocketChannels
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonReceivedCanonicalSocketGaussian (value)

theorem paidAir {G:Gauge}{n:Side}{V α ι ι':Type}[DecidableEq V]{J:Marker.Census V}{p p':Passport n V}
    (U:ι→Row p J G α)(M:ι'→Row p' J G α)(roots:p=p')(indices:ι=ι')(ink:HEq U M)
    (x:α)(grades:V→ℕ)(L:Layout G)(tape:Finset Age):
    Air.craft U (fun j=>(U j).paint x) grades L tape=Air.craft M (fun j=>(M j).paint x) grades L tape:=by
  subst p'
  subst ι'
  obtain rfl:=eq_of_heq ink
  rfl

private theorem page_site {n:Side}(x:Site n)(p:Fin (Pages n n)):
    (page (dvd_refl n.val) x p).val=x:=by
  have same:=(page (dvd_refl n.val) x p).property
  simp only [parcel,Finset.mem_filter,Finset.mem_univ,true_and] at same
  have splitting (y:Site n):splitter (dvd_refl n.val) y=y:=by
    simpa only [wrap_lift] using Macrame.branch (dvd_refl n.val) (lift y)
  exact (splitting _).symm.trans same

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){h:Fin 3→ℕ}(pt:Fin 3→Chamber)
  (q:(j:Fin 3)→Choice R d j)(hd:∀j,d j≤WilsonOriginalThermometerPalette.levels j)
  (N i per:ℕ)(hi:i<N)(o:Fin 3→Site (fine R i per))(σ:ℝ)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (x:Affinity.Wallet disks)(a:Fin 3 → Lattice.Cover)(home:∀j,wrap (fine R i per) (a j)=o j)
local notation "M" => row R d q hd o σ
local notation "J" => Stock.census (Fin 3)
local notation "l₀" => WilsonOriginalThermometerPalette.levels
local notation "K" => model R N i per hi

include home in
theorem original {ι:Type}{p:Passport (fine R i per) (Fin 3)}
    (U:ι→Row p (J) G (Affinity.Wallet disks))(roots:p=Passport.point o)(indices:ι=Fin 3)(ink:HEq U M)
    {w:Fin 3→ℝ}{width fare:ℝ}{order seats shelf:ℕ}(stock:Scene.Armada M w l₀ width fare order seats shelf)
    (width0:0<width) {m e:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e quiet π Γ)(lo:m ≤ i){τ cash:ℝ}
    (funded:Issued R N (i+1) e (quiet (i+1)) τ cash)(legal:Legal (Step.tape (e+2)) (π (i+1)))
    (b:Stationary.Link G (coarse R i per))(r:ℕ)(grade:r ≤ e+2):
    let B:=Stationary.arm G _ 1 b
    let filed:=Bulk.Fk (K) F tag (Air.craft U (fun j=>(U j).paint x) l₀ (π (i+1)) (Step.tape (e+2))) B r
    let income:=fun ζ=>value (h:=h) R d pt q N i per hi F x B ζ
      (fun _:Fin (Pages (fine R i per) (fine R i per))=>a) r
    let cov:=(K).covariance F tag
    let computed:=WilsonOriginalGaussianPaidTable.table (Board (J) r) cov income
    ratio filed=ratio computed ∧ logMarked filed=logMarked computed ∧
      ∀s,MeasureTheory.Integrable (WilsonOriginalGaussianPaidTable.presented (Board (J) r) income s)
        (Gaussian.cloud cov):=by
  have located (p:Fin (Pages (fine R i per) (fine R i per))) (j:Fin 3):
      wrap (fine R i per) (a j)=(FVA1Physical.TwoReset.copy (dvd_refl (fine R i per).val) (M j) p).center:=by
    rw [home]
    exact (page_site (o j) p).symm
  have h:=WilsonReceivedCanonicalSocketGaussian.original (h:=h) R d pt q hd o σ N i per hi F tag
    (dvd_refl (fine R i per).val) x (π (i+1)) (Step.tape (e+2)) (fun _=>a) located
    stock width0 legal course lo funded b r grade
  rw [paidAir U M roots indices ink x l₀ (π (i+1)) (Step.tape (e+2))]
  rw [WilsonThermometerPositionFilmSelf.original] at h
  exact h

end YM.Integration.WilsonReceivedCanonicalSocketSelf
