import YM.Integration.WilsonOriginalEarnedUnaryPage

/-! Gauge- and source-specific physical finite normalization on a shared, deposited vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalEarnedUnarySheet
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Order AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series Series.Radial Series.Tested
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos Next.Rank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative credit)
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  {V:Type}[DecidableEq V][Fintype V]{C:Marker.Census V}(Y:Bulk.Colors C G (fine R i per))
local notation "S" => step R i per
local notation "K" => model R N i per hi
local notation "φ" => relative R N i per hi F (covered R N i per)
variable (B₀:Stationary.Link G (coarse R i per))
local notation "B" => Stationary.arm G (coarse R i per) 1 B₀


open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonOriginalSingleGaussianPass (deposit read_deposit)
open PhysicalForestMarkedRay
open WilsonOriginalSingleGaussianReceipt
variable (s₀:Hot C)(a:ℂ)(T:PChart G (fine R i per))(r:ℕ)
local notation "word" => WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F T
local notation "rng" => Woods G (coarse R i per)
local notation "arg" => saddle R N i per F


open WilsonOriginalEarnedUnaryPage (Ray page)
open WilsonOriginalSingleGaussianDivision (row)
open WilsonOriginalSingleMarkedRegister (token)
open WilsonVacuumPreResetFiniteRegister (register)
open OriginalRadialSeries (observed)
local notation "q₀" => ((K).covariance F tag)
local notation "ink" => WilsonOriginalFoldedMarkedRightColumn.filed R N i per F

theorem normalized (simple:G.Simple){m e:ℕ}(h:ℕ)(hr:r≤e+2)(sp:shellK h T)(pure:∀d,Pure (T d))
    {Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}(course:Read R N m e Z π Γ)(lo:m ≤ i)
    {σ cash:ℝ}(bank:Issued R N (i+1) e (Z (i+1)) σ cash)(well:Bulk.Well Y)
    (ray:Ray R N i per hi F Y B s₀ a T r):
    let W:=QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) Y
    let actual:=Bulk.Fk K F tag W B r
    let out:=token C r s₀.val*(a • register C r (observed (flatten B) (flash (ink h T))))
    ratio actual=1+out ∧ logMarked actual=out:=by
  intro W actual out
  let P:=page R N i per hi F tag Y B s₀ a T r e (Z (i+1)) well ray
  have hrow :row P q₀=a • register C r (observed (flatten B) (flash (ink h T))):=by
    have hh:=WilsonOriginalFoldedMarkedRightColumn.normalized R N i per hi F tag simple h T sp pure
    have recog:=WilsonOriginalSingleGaussianDivision.identified P q₀ ((K).symm F tag)
      (fun _:Unit=>observed (flatten B) (flash (ink h T))) (by
        intro u
        change observed (flatten B) (Wick _ q₀ (raiseE φ * word)) = _
        rw [hh,map_mul]
        rfl)
    have amp:P.amplitude default=a:=rfl
    simpa only [Fintype.sum_unique,amp] using recog
  have proposed:=WilsonOriginalEarnedUnaryDriver.original R N i per hi F tag Y course lo well bank B₀ r hr
  have last :token C r P.source*row P q₀=out:=congrArg (token C r s₀.val*·) hrow
  exact ⟨proposed.1.trans ((WilsonOriginalSingleGaussianDivision.normalized P q₀ ((K).symm F tag)).trans (congrArg (1+·) last)),
    proposed.2.trans ((WilsonOriginalSingleGaussianDivision.logarithm P q₀ ((K).symm F tag)).trans last)⟩

theorem projected (simple:G.Simple){m e:ℕ}(h:ℕ)(hr:r≤e+2)(sp:shellK h T)(pure:∀d,Pure (T d))
    {Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}(course:Read R N m e Z π Γ)(lo:m ≤ i)
    {σ cash:ℝ}(bank:Issued R N (i+1) e (Z (i+1)) σ cash)(well:Bulk.Well Y)
    (ray:Ray R N i per hi F Y B s₀ a T r)(j:ℕ)(hj:j≤r):
    let W:=QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) Y
    let actual:=Bulk.Fk K F tag W B r
    (Order.observe C r (logMarked actual) j).part s₀.val=
      a * ((coeff j (observed (flatten B) (flash (ink h T))):ℝ):ℂ):=by
  intro W actual
  have done:=normalized R N i per hi F tag Y B₀ s₀ a T r simple h hr sp pure course lo bank well ray
  let P:=observed (flatten B) (flash (ink h T))
  rw [done.2]
  rw [Order.observe,if_pos hj]
  change (j.factorial:ℂ)⁻¹ * (token C r s₀.val * (a • register C r P)).part (Join.pair s₀.val (Order.pick r j))=_
  rw [mul_smul_comm]
  change (j.factorial:ℂ)⁻¹ * (a*(token C r s₀.val*register C r P).part (Join.pair s₀.val (Order.pick r j)))=_
  rw [WilsonOriginalSingleMarkedRegister.token_read C r _ _ _ _ (WilsonOriginalSingleMarkedRegister.clean C r P),
    if_pos rfl,WilsonVacuumPreResetFiniteRegister.read,Order.picked r hj,if_pos rfl]
  have nonzero:(j.factorial:ℂ)≠0:=by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [←mul_assoc,mul_comm _ a,mul_assoc,←mul_assoc (j.factorial:ℂ)⁻¹,(inv_mul_cancel₀ nonzero),one_mul]

end YM.Integration.WilsonOriginalEarnedUnarySheet
