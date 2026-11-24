import YM.Integration.WilsonOriginalRawPinnedPage
import YM.Integration.WilsonOriginalPinnedGaussianGrade
import YM.Integration.WilsonOriginalEarnedFoldedUnary

/-! The actual original upper amplitude returned on a previously occupied single name
inside a several-name census. The named pre-reset finite Wilson tensors retain each
charged row and the true upper quiet before the next birthday. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRawPinnedFinite
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Comparison.Density.RenderM NativePaidPacketColors MergeProof MergeProof.Accent
open PertExtension Series Series.Radial Series.Tested RegulatorIR RegulatorIR.FVAAlt2
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open ActualRunCalibrationTests OriginalSourceJetAddresses FundedOriginalMarkedInput
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner


open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open Order AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open Next.SectorChange

variable {G:Gauge}(R:Run G){deck:MS.Local.Physical.Deck G}(N i per:ℕ)(hi:i < N)
  {n:ℕ}{hn:n ≤ i + 1}{V:Type}[DecidableEq V][Fintype V]
  (Q:MS.Land.Prescription deck)(D:ActualRunQlocalNativeTuple.Datum R per (i + 1) n hn V)
  (u:V→MS.Rake.Label deck)(μ:ℝ)(orders:V→ℕ) (x:TestSpace (ActualRunQlocalNativeTuple.orbit D))
local notation "C" => Stock.census V
local notation "P" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "v₀" => (Bulk.Colors.noHole G (R.family.side (i + 1) per) C).vac
local notation "Y" => NativePaidPacketColors.colors P v₀ x
local notation "S" => step R i per
local notation "K" => model R N i per hi

include hi in
private theorem legal : Bulk.Well Y :=by
  have H:=ActualOriginalQPackets.packets_paid Q D u μ orders N ((levels R).budget (i + 1))
    (fun _=>1) 1 zero_lt_one (fun _=>zero_lt_one)
  have law:=(Bulk.Colors.no_hole G (R.family.side (i + 1) per) C).1
  exact NativePaidPacketColors.colors_well H (ActualRunKernelPackets.regulator_pos R N per (i+1) hi).ne' v₀ law.suppose_vac law.natural law.envelope _

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)
variable (z:Precision.Key F G→ℝ)
local notation "M" => saddle R N i per F

open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))


open PhysicalForestMarkedRay
open WilsonOriginalJointForestRay (forward)
open WilsonOriginalFoldedUnarySourceEra (data)


open WilsonOriginalSingletonPin (seat)
open WilsonOriginalRawForestRays (paper)
open WilsonOriginalSingleForestPage (Single recorded)
local notation "J" => Stock.census Unit
local notation "o" => (⟨(J).fire (),Finset.singleton_nonempty ()⟩:Hot (J))
variable (v:V)
local notation "projected" => Sources.pin (seat v) Y
local notation "amp" => weight D u N ((C).fire v)
local notation "papers" => paper (R:=R) (i:=i) (per:=per) Q D u μ orders x


open WilsonOriginalEarnedFoldedUnary (independent)
open WilsonOriginalSingleGaussianReceipt (numerator mass)
open WilsonOriginalSingleGaussianDivision (row identified)
open OriginalRadialSeries (observed)
open WilsonOriginalFoldedUnarySourceEra (reserve)
local notation "q₀" => ((K).covariance F tag)
local notation "B₁" => (fun B₀=>Stationary.arm G (coarse R i per) 1 B₀)

theorem original (simple:G.Simple)(k:V→ℕ) {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}(bank:Issued R N (i+1) e (Z (i+1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(r:ℕ)(hr:r≤e+2)(j:ℕ)(hj:j≤r):
    let W₀:=NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x
    (Order.observe (C) r (Order.logMarked (Bulk.Fk K F tag W₀ (B₁ B₀) r)) j).part ((C).fire v)=
      ∑z:Source D u,amp z*((coeff j (observed (flatten (B₁ B₀))
        (flash (independent R N i per Q D u μ orders x F k z))):ℝ):ℂ):=by
  intro W₀
  let well:=Sources.well (seat v) Y (legal R N i per hi Q D u μ orders x)
  let rays:=WilsonOriginalRawPinnedPage.original R N i per hi Q D u μ orders x F tag (B₁ B₀) v r
  let W:=recorded R N i per hi F tag projected (B₁ B₀) o amp papers r e (Z (i+1)) well rays
  let T:=fun z:Source D u=>flash (independent R N i per Q D u μ orders x F k z)
  have paid (z:Source D u):numerator W q₀ z=mass W q₀*T z:=by
    let seed:=data (R:=R) (i:=i) (per:=per) Q D u μ orders x z
    have ticket:=WilsonOriginalFoldedUnarySourceEra.admitted (R:=R) (i:=i) (per:=per) Q D u μ orders x k z
    exact WilsonOriginalFoldedMarkedRightColumn.normalized R N i per hi F tag simple
      (reserve (R:=R) (i:=i) (per:=per) D u k z) (seed.1 (fine R i per)) (ticket.span _) (ticket.pale _)
  have delivered:=identified W q₀ ((K).symm F tag) (fun z=>observed W.B (T z)) (fun z=>by rw [paid,map_mul])
  have read:=WilsonOriginalRawPinnedPage.returned R N i per hi Q D u μ orders x F tag v course lo bank B₀ r hr j hj
  change (Order.observe (C) r (Order.logMarked (Bulk.Fk K F tag W₀ (B₁ B₀) r)) j).part ((C).fire v)=
      (Order.observe (J) r (WilsonOriginalSingleMarkedRegister.token (J) r ((J).fire ()) * row W q₀) j).part ((J).fire ()) at read
  rw [delivered] at read
  exact read.trans (WilsonOriginalPinnedGaussianGrade.original (J) r ((J).fire ()) amp (fun z=>observed W.B (T z)) j hj)

end YM.Integration.WilsonOriginalRawPinnedFinite
