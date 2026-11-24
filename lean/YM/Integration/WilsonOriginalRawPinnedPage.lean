import YM.Integration.WilsonOriginalSingletonPin
import YM.Integration.WilsonOriginalSingleForestPage

/-! The old Q projection on the funded original upper finite block, preserving every
other enrolled name in the ambient class. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRawPinnedPage
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

private theorem sole (s:Hot (J)):s.val=(J).fire ():=by
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro q _
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  · obtain ⟨q,hq⟩:=s.prop
    cases q
    exact Finset.singleton_subset_iff.mpr hq

include tag in
theorem original (r:ℕ):
    Single R N i per hi F projected B o amp papers r:=by
  intro s j _ z
  have eq : ((seat v).look s).val=(C).fire v:=by
    change (seat v).share s.val=(C).fire v
    rw [sole s,(seat v).fire]
    rfl
  have heard:=WilsonOriginalRawForestRays.original R N i per hi Q D u μ orders x F tag B ((seat v).look s) j z
  rw [eq] at heard
  rw [if_pos (sole s)]
  exact heard

local notation "q₀" => ((K).covariance F tag)
open WilsonOriginalSingleGaussianDivision (row)
open WilsonOriginalSingleMarkedRegister (token)

theorem returned {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}(bank:Issued R N (i+1) e (Z (i+1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(r:ℕ)(hr:r≤e+2)(j:ℕ)(hj:j≤r):
    let held:=Stationary.arm G (coarse R i per) 1 B₀
    let W:=recorded R N i per hi F tag projected held o amp papers r e (Z (i+1))
      (Sources.well (seat v) Y (legal R N i per hi Q D u μ orders x))
      (original R N i per hi Q D u μ orders x F tag held v r)
    (Order.observe (C) r (Order.logMarked (Bulk.Fk K F tag
        (NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x) held r)) j).part ((C).fire v)=
      (Order.observe (J) r (WilsonOriginalSingleMarkedRegister.token (J) r (o).val*WilsonOriginalSingleGaussianDivision.row W q₀) j).part ((J).fire ()):=by
  intro held W
  have well:=Sources.well (seat v) Y (legal R N i per hi Q D u μ orders x)
  have read:=WilsonOriginalSingleForestPage.original R N i per hi F tag projected o amp papers r course lo well bank B₀ hr
    (original R N i per hi Q D u μ orders x F tag held v r)
  have high:=WilsonOriginalSingletonPin.original K F tag v held r
    (NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x) j hj
  exact high.trans (congrArg (fun T=> (Order.observe (J) r T j).part ((J).fire ())) read.2)

end YM.Integration.WilsonOriginalRawPinnedPage
