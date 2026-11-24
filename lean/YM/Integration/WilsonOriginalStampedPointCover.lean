import YM.Integration.FVA1Physical.TwoReset.ClubAssembly
import YM.Integration.WilsonOriginalStampedPointPages
import YM.Integration.WilsonOriginalStampedPrimerCover
import YM.Integration.WilsonNeutralPointCopies

/-! Original pre-reset FkCover on every genuine finite covering period of a fixed original post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalStampedPointCover
open Function Finset Lattice RG Laurent Wilson Tree Stationary PhysicalNext.Repeat.Legato FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Exterior Lotus Shore Gorge
open Rift Lava Kemp Pose Glide Dawn Rial Roof Planned.PrimaryIntegral295 Source Source.Drops Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonVacuumPreResetStationaryChange
open WilsonOlderFreshGraphPainter WilsonOriginalPrimerReplicatedInk
open WilsonOriginalPrimerFiledPages (sites)
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe 
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink Primitives.TwoWave
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetDepositedGeometric WilsonOriginalOccupiedForestIntegral
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalSingleMarkedRegister (token)
open WilsonVacuumPreResetFiniteRegister (register)
open OriginalRadialSeries (observed)
open Comparison.RG02.Cumulants Comparison.RG02.Assembly Order WilsonOriginalEarnedUnaryPage
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner


open private tariff from YM.Integration.WilsonOriginalStampedPrimerCover

variable {G:Gauge}{d D Q:ℕ}(R:Run G)(a:hue G)(depth:d<D)
variable {U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)
variable (N i per:ℕ)(hi:i<N)(letter:Letter (R.family.labels.level d))(f:Studio D)
local notation "V" => R.family.path.levels
local notation "wood" => (fun j:ℕ=>Flat.routes ((V).clock.op j 0).patch)
local notation "A₀" => destination V N i
local notation "n₀" => R.family.side i per
local notation "f₀" => R.family.side (i+1) per
local notation "repeats" => Covers (V).S i n₀
variable (digit:∀j,Site (R.family.S.block j))
local notation "ticketₚ" => (Prod.mk (WilsonPointChildFiledPress.Tour.mk N hi digit) f : WilsonOlderFreshPointGauge.Ballot R (i+1) D)
variable {P P':Earn.Passport (R.family.side (i+1) per) Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)
variable (E:Unit→Set ℂ)(x:Affinity.Wallet E){I:Type}(M:I→Earn.Row P' H G (Affinity.Wallet E))
variable {σ:ℝ}(C:WilsonOlderFreshGraphSlate.Copy G d Q σ)
include grant in
theorem original (passport:P'=P)(names:I=C.Roster)(rows:HEq M (C.rows S E))
    (cap:∀t,‖value E t‖≤1)(σ0:0<σ)(filed:WilsonOlderFreshPointCommission.Published R wood a depth (i+1) letter (ticketₚ) C)
    (tags:∀j n,(primary ((V).clock.op j 0).patch (V).clock.kernel n).Choices)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {m e:ℕ}(r:ℕ)(hr:r≤Q)(height:r≤e+2)
    {Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}(course:Read R N m e Z π Γ)(lo:m ≤ i)
    {μ cash:ℝ}(bank:Issued R N (i+1) e (Z (i+1)) μ cash)(legal:Legal (Step.tape (e+2)) (π (i+1)))
    (F:∀c:repeats,Forest ((V).clock.op i c.val).ratio):
    ∃ (F':∀c:repeats,Forest (Flat.primary (A₀).patch (V).clock.kernel (R.family.side i c.val)).ratio),
    (∀c,HEq (F c) (F' c)) ∧
    ∀(u:∀c:repeats,(Flat.primary (A₀).patch (V).clock.kernel (R.family.side i c.val)).Choices)
      (tag:∀c:repeats,((V).clock.op i c.val).Choices)(j:ℕ),j≤r → ∀(B:Link G n₀)(c:repeats),
      (FVA1Physical.TwoReset.FkCover (n:=per) R hi (π (i+1)) (Step.tape (e+2)) r M (fun _=>d) x n₀ dvd_rfl F tag B j c).part (submitted S).val=
      value E x * (WilsonNeutralPointCopies.phase R wood a depth digit N i n₀ (R.family.side i c.val) c.prop
        (F' c) (u c) letter f (sites S.center (n₀*(A₀).L)) j B:ℝ):=by
  choose F' same run using fun c:repeats=>WilsonOriginalStampedPointPages.appointed R a depth grant N i c.val hi
    letter f digit (tiled R dvd_rfl c) S E x M C passport names rows cap σ0 filed tags simple v funded r hr height
    course lo bank legal (F c)
  refine ⟨F',same,?_⟩
  intro u tag j hj B c
  let larger:=R.family.side i c.val
  let link:=convey (coverWin c.prop) B
  let b:=FreeResolvent.flatten (Stationary.arm G larger 1 link)
  let eval (z:Site (larger*(A₀).L)):=MvPolynomial.eval b (coeff j (WilsonNeutralPointAngle.reading
    R wood a depth digit N i larger (F' c) (u c) letter f z))
  have read:=(run c (u c) (tag c) link).2.2 j hj
  have sizes (p:ℕ): R.family.side (i+1) p=R.family.side i p*(A₀).L:=
    Subtype.ext ((V).clock.op i p).sizes
  have h':=tiled R (n:=per) (m:=i) dvd_rfl c
  have price:=tariff (sizes per) (sizes c.val) c.prop h' (subdiv_dvd (Ratio.mk (A₀).L rfl : Ratio n₀ (n₀*(A₀).L)) (Ratio.mk (A₀).L rfl : Ratio larger (larger*(A₀).L)) rfl c.prop) eval S.center
  let vsum:=∑b:Fin (Pages f₀ (R.family.side (i+1) c.val)),eval (sites (page h' S.center b).val (larger*(A₀).L))
  change (Pages n₀ larger:ℝ)⁻¹*vsum=WilsonNeutralPointCopies.phase R wood a depth digit N i n₀ larger c.prop
    (F' c) (u c) letter f (sites S.center (n₀*(A₀).L)) j B at price
  have heard:
      (Order.observe H r (logMarked (Bulk.Fk (model R N i c.val hi) (F c) (tag c)
        (copyColor h' M (fun _=>d) (fun j=>(M j).paint x) (π (i+1)) (Step.tape (e+2)))
        (Stationary.arm G larger 1 link) r)) j).part (submitted S).val=value E x*(vsum:ℝ):=by
    simpa only [OriginalRadialSeries.observed,coeff_map,map_sum] using read
  rw [FVA1Physical.TwoReset.FkCover]
  change ((Pages n₀ larger:ℝ)⁻¹:ℝ) • ((Order.observe H r (_) j).part (submitted S).val)=_
  rw [heard,←price,Complex.ofReal_mul,Complex.real_smul]
  ring

end YM.Integration.WilsonOriginalStampedPointCover
