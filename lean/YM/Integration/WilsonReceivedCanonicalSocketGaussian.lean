import YM.Integration.WilsonReceivedCanonicalSocketChannels
import YM.Integration.WilsonOriginalThreeGaussianReturn

/-! The finite ordinary Gaussian of the actual fixed-site K trial with its separately supplied old vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalSocketGaussian
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
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){h:Fin 3→ℕ}(pt:Fin 3→Chamber)
  (q:(j:Fin 3)→Choice R d j)(hd:∀j,d j ≤ WilsonOriginalThermometerPalette.levels j)
  {n:Side}(o:Fin 3→Site n)(σ:ℝ)(N i per:ℕ)(hi:i<N)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(copying:n.val∣(fine R i per).val)
  (x:Affinity.Wallet disks)(L:Layout G)(tape:Finset Age)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "M" => row R d q hd o σ
local notation "J" => Stock.census (Fin 3)
local notation "l₀" => WilsonOriginalThermometerPalette.levels
local notation "Y" => copyColor copying M l₀ (fun j=>(M j).paint x) L tape
local notation "K" => model R N i per hi
local notation "S" => step R i per
local notation "A" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "Pgs" => Fin (Pages n (fine R i per))
local notation "κ" => (fun j=>contact (h j))
variable (addresses:Fin (Pages n (fine R i per)) → Fin 3 → Lattice.Cover)
  (located:∀p j,wrap (fine R i per) (addresses p j)=(FVA1Physical.TwoReset.copy copying (row R d q hd o σ j) p).center)


def value (r:ℕ)(s:Hot (Board (J) r)):ℂ:=
  let grade:=(Join.right s.val).val.card
  (grade.factorial:ℂ)*(if (Join.left s.val).val.Nonempty then
    ∑p:Pgs,∑j:Fin 3,if (J).fire j=Join.left s.val then probe j x*
      seed (h:=h) R d pt q N i per hi F B z addresses p j grade else 0
    else Cloud.paint z (SignedRegisteredMarkedProgram.register F B
      (coeff grade (relative R N i per hi F (covered R N i per)))))

include located in
theorem channel {w:Fin 3→ℝ}{width fare:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w l₀ width fare order seats shelf)(width0:0<width)(legal:Legal tape L)
    (e:ℕ)(quiet:SeriesA G)(r:ℕ)(s:Hot (Board (J) r)):
    Cloud.paint z (driver R N i per hi F tag (Y) B e quiet r s)=
      value (h:=h) R d pt q N i per hi F x B z addresses r s:=by
  have well:Bulk.Well (Y):=(copy_standard copying M l₀ (fun j=>(M j).paint x) L tape
    (Air.license M _ l₀ w stock width0 (fun j=>stock.honor j x)) legal).1
  rw [WilsonOriginalForestDriverReading.original R N i per hi F tag (Y) B z e quiet well r s]
  unfold value
  by_cases occupied:(Join.left s.val).val.Nonempty
  · simp only [if_pos occupied,dif_pos occupied]
    apply congrArg (((Join.right s.val).val.card.factorial:ℂ)*·)
    exact WilsonReceivedCanonicalSocketChannels.original (h:=h) R d pt q hd o σ N i per hi F tag copying
      x L tape B z addresses located stock width0 legal ⟨Join.left s.val,occupied⟩ _
  · simp only [if_neg occupied,dif_neg occupied]

include located in
theorem original {w:Fin 3→ℝ}{width fare:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w l₀ width fare order seats shelf)(width0:0<width)(legal:Legal tape L)
    {m e:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e quiet π Γ)(lo:m ≤ i){τ cash:ℝ}
    (funded:Issued R N (i+1) e (quiet (i+1)) τ cash)
    (b:Stationary.Link G (coarse R i per))(r:ℕ)(grade:r ≤ e+2):
    let B₀:=Stationary.arm G _ 1 b
    let filed:=Bulk.Fk (K) F tag (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) (Y)) B₀ r
    let income:=fun ζ=>value (h:=h) R d pt q N i per hi F x B₀ ζ addresses r
    let covariance:=(K).covariance F tag
    let computed:=WilsonOriginalGaussianPaidTable.table (Board (J) r) covariance income
    ratio filed=ratio computed ∧ logMarked filed=logMarked computed ∧
      ∀s,MeasureTheory.Integrable (WilsonOriginalGaussianPaidTable.presented (Board (J) r) income s)
        (Gaussian.cloud covariance):=by
  intro B₀ filed income covariance computed
  have hit (ζ:Precision.Key F G→ℝ)(s:Hot (Board (J) r)):
      Cloud.paint ζ (driver R N i per hi F tag (Y) B₀ e (quiet (i+1)) r s)=income ζ s:=
    channel (h:=h) R d pt q hd o σ N i per hi F tag copying x L tape B₀ ζ addresses located
      stock width0 legal e (quiet (i+1)) r s
  have read:=WilsonOriginalGaussianPaidTable.original (Board (J) r) covariance income
    ((K).symm F tag) ((K).positive F tag).posSemidef _ hit
  have paid:=WilsonOriginalAllInputForestDriver.original R N i per hi F tag (Y) course lo funded b r grade
  exact ⟨paid.1.trans (congrArg Order.ratio read.1),paid.2.trans (congrArg Order.logMarked read.1),read.2⟩

end YM.Integration.WilsonReceivedCanonicalSocketGaussian
