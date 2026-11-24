import YM.Integration.WilsonOriginalChargedRawWick
import YM.Integration.WilsonOriginalRelativeFoldedQuiet

/-! The funded raw source on its own dated relative Gaussian chart with the independently folded quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRegisteredFoldedDrivers
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

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)
local notation "M" => saddle R N i per F

open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))


open WilsonOriginalChargedRawWick WilsonOriginalRelativeFoldedQuiet
open WilsonVacuumPreResetOriginalOutput (covered)

def folded (r:ℕ)(s:Hot (Board C r)) : MvPolynomial (Precision.Key F G) ℂ :=
  let d := (Join.right s.val).val.card
  (d.factorial:ℂ) • if (Join.left s.val).val.Nonempty then
    charged R N i per hi Q D u μ orders x F B d (Join.left s.val)
  else SignedRegisteredMarkedProgram.register F B
    (coeff d (relative R N i per hi F (covered R N i per)))

private theorem linear (Z:SeriesA G)(e d:ℕ){σ cash:ℝ}
    (bank:Issued R N (i+1) e Z σ cash)(hd:d<3+e) :
    SignedRegisteredMarkedProgram.register F B (coeff d (opened R N i per hi F Z)) =
      SignedRegisteredMarkedProgram.register F B
        (coeff d (relative R N i per hi F (covered R N i per))) +
      MvPolynomial.C (((coeff d (credit (WilsonVacuumPreResetDepositedRay.filed R N i per Z) (covered R N i per))):ℝ):ℂ) :=by
  have h:=WilsonOriginalRelativeFoldedQuiet.original R N i per hi F e Z bank d hd
  rw [map_add] at h
  rw [h,map_add]
  congr 1
  simp [WilsonCoeffUV.Blue.holdUp,WilsonCoeffUV.Blue.holdUpPoly,soil,
    PowerSeries.coeff_map,SignedRegisteredMarkedProgram.register]

variable {J:Census V}

theorem vacant (p:PowerSeries ℝ)(r:ℕ) :
    bottom J r (register J r p)=register J r p :=by
  apply Join.both_parts
  intro t u
  rw [bottom_value,WilsonVacuumPreResetFiniteRegister.read,WilsonVacuumPreResetFiniteRegister.read]
  split_ifs <;> simp_all

theorem zero (p:PowerSeries ℝ)(r:ℕ)(hz:constantCoeff p=0) :
    (register J r p).part (Board J r).quiet=0 :=by
  rw [←Join.pair_quiet,WilsonVacuumPreResetFiniteRegister.read,if_pos rfl]
  simp [coeff_zero_eq_constantCoeff_apply,hz,Census.quiet]

theorem credit_zero {n':Side}(U U':WilsonCoeffUV.PChart G n') :
    constantCoeff (credit U U')=0 :=by
  rw [←coeff_zero_eq_constantCoeff_apply,credit,correction,coeff_mk,if_pos rfl]

theorem actual (Z:SeriesA G)(e r:ℕ){σ cash:ℝ}
    (bank:Issued R N (i+1) e Z σ cash)(hr:r≤e+2)(s:Hot (Board C r)):
    atoms R N i per hi Q D u μ orders x F B Z r s =
      folded R N i per hi Q D u μ orders x F B r s +
        MvPolynomial.C ((register C r (credit (WilsonVacuumPreResetDepositedRay.filed R N i per Z) (covered R N i per))).part s.val) :=by
  let d:=(Join.right s.val).val.card
  let fees:=credit (WilsonVacuumPreResetDepositedRay.filed R N i per Z) (covered R N i per)
  have amount (p:PowerSeries ℝ) : (register C r p).part s.val=
      (d.factorial:ℂ)*(if Join.left s.val=(C).quiet then ((coeff d p:ℝ):ℂ) else 0) :=by
    simpa only [Join.pair_reunite] using WilsonVacuumPreResetFiniteRegister.read C r p (Join.left s.val) (Join.right s.val)
  unfold atoms folded
  dsimp only []
  rw [amount]
  by_cases use:(Join.left s.val).val.Nonempty
  · rw [if_pos use,if_pos use,if_neg ((hot_iff_ne _).1 use),mul_zero,map_zero,add_zero]
  · have hc:Join.left s.val=(C).quiet:=of_not_not (mt (hot_iff_ne _).2 use)
    rw [if_neg use,if_neg use,if_pos hc]
    have h:=linear R N i per hi F B Z e d bank (by have:=Order.order_limit r (Join.right s.val);dsimp [d];omega)
    rw [h,smul_add]
    congr 1
    rw [map_mul,Algebra.smul_def]
    rfl

end YM.Integration.WilsonOriginalRegisteredFoldedDrivers
