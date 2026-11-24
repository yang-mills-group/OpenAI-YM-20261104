import YM.Integration.WilsonOriginalSingleGaussianPass
import YM.Integration.WilsonOriginalGaussianFibre

/-! One genuinely funded new Wilson source in the complete finite normalized conditional. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedUnaryIncome
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
local notation "P₀" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "v₀" => (Bulk.Colors.noHole G (R.family.side (i + 1) per) C).vac
local notation "Y" => NativePaidPacketColors.colors P₀ v₀ x
local notation "S" => step R i per
local notation "K" => model R N i per hi

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)

local notation "M" => saddle R N i per F

open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))

open WilsonCoeffUV.Bank.Mosaic.Near IndependentSourcePathFamily OriginalMarkedSourceComet FundedOriginalMarkedInput


variable [Subsingleton V](v:V)
local notation "φ" => WilsonOriginalRelativeFoldedQuiet.relative R N i per hi F
  (WilsonVacuumPreResetOriginalOutput.covered R N i per)
local notation "word" => WilsonOriginalRegisteredRawPage.field R N i per hi Q D u μ orders x F
local notation "cᵢ" => WilsonOriginalChargedRawJet.weight D u N ((C).fire v)
local notation "driver" => WilsonOriginalRegisteredFoldedDrivers.folded R N i per hi Q D u μ orders x F B

private theorem unique (t:(C).Mode)(h:t.val.Nonempty): t=(C).fire v:=by
  apply Subtype.ext
  ext a
  change a∈t.val ↔ a∈({v}:Finset V)
  rw [Finset.mem_singleton]
  exact ⟨fun _=>Subsingleton.elim a v,fun _=>by
    obtain ⟨b,hb⟩:=h
    exact Subsingleton.elim b a ▸ hb⟩

theorem income (r:ℕ)(s:Hot (Board C r))(z:Precision.Key F G→ℝ):
    Cloud.paint z (driver r s)=
      (WilsonOriginalSingleGaussianPass.deposit r (flatten B) φ word cᵢ z ((C).fire v)).part s.val:=by
  rw [←Join.pair_reunite s.val,WilsonOriginalSingleGaussianPass.read_deposit]
  by_cases hs:(Join.left s.val).val.Nonempty
  · have eq:=unique v (Join.left s.val) hs
    have hn:= (hot_iff_ne (Join.left s.val)).mp hs
    simp only [WilsonOriginalRegisteredFoldedDrivers.folded,if_pos hs,if_neg hn,if_pos eq,zero_add,
      map_smul, smul_eq_mul]
    rw [WilsonOriginalRegisteredRawPage.driver,eq,map_sum,Finset.mul_sum]
    simp_rw [map_smul,smul_eq_mul,WilsonOriginalGaussianFibre.reading]
    apply sum_congr rfl
    intro a _
    exact (mul_assoc _ _ _).symm
  · have hq:Join.left s.val=(C).quiet:=of_not_not (mt (hot_iff_ne _).2 hs)
    have hn:Join.left s.val≠(C).fire v:=by
      intro eq
      exact hs (eq.symm ▸ (show ((C).fire v).val.Nonempty from singleton_nonempty _))
    simp only [WilsonOriginalRegisteredFoldedDrivers.folded,if_neg hs,if_pos hq,if_neg hn,add_zero,
      map_smul,smul_eq_mul,WilsonOriginalGaussianFibre.reading]

end YM.Integration.WilsonOriginalFoldedUnaryIncome
