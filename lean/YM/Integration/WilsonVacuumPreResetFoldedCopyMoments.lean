import YM.Integration.WilsonVacuumPreResetFundedOutput
import YM.Integration.WilsonVacuumPreResetTorusFundedMassLimit

/-! The genuine finite history and the finite update on the folded vacuum have the same
centered positive-rank coefficient after the fixed-cutoff copy limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFoldedCopyMoments
open AllOrder AllOrder.Floe AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Classical Topology BigOperators

open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port PhysicalNext.Repeat.Legato FVA1Physical.MixedResets
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero Comparison.RG02

open WilsonVacuumPreResetTorusRegister WilsonVacuumPreResetTorusMaterial
open Comparison.RG02.Order Next.SectorChange Marker Exterior
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetTorusSeason WilsonVacuumPreResetTorusMoment
open WilsonVacuumPreResetTorusSeasonMoments
open WilsonVacuumPreResetTorusActionRead (originalAction corrected)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (Covers coverFilter coverWin)
open WilsonCoeffUV.Winding
open WilsonVacuumPreResetTorusCoverAction (Cover sheets)
variable {G:Gauge}(R:Run G)

theorem inlet (simple:G.Simple){N m:ℕ}(hm:m≤N)(i r:ℕ):
    let A:=R.family.path.levels
    let P:=actionW A R.metals.O N m
    Yields (fun n=>emera P n i r) (P i r):=by
  dsimp only
  let A:=R.family.path.levels
  let P:=actionW A R.metals.O N m
  have receipt:LocalRatio R.metals.O:=(RunFormalChain.fromRun R).receipt
  cases r with
  | zero=>
    have empty:=congrFun (congrFun (catchment A R.metals.O simple receipt hm).empty i) 0
    have h:P i 0=0:=empty.symm
    rw [show actionW R.family.path.levels R.metals.O N m i 0=0 from h]
    exact Yields.zero
  | succ l=>
    have law:=(old A R.metals.O simple receipt N m hm).patch i (l+1)
    obtain ⟨σ,M,positive,bill⟩:=law.cover
    exact lagoon_yields bill positive law.road

theorem output (simple:G.Simple){N m:ℕ}(hm:m<N)(i r:ℕ):
    let A:=R.family.path.levels
    let Ñ:=R.metals.O
    Yields (fun n=>coil0 A Ñ m N n i r) (freshet A Ñ N m i r):=by
  dsimp only
  let A:=R.family.path.levels
  let Ñ:=R.metals.O
  let U:=emera (actionW A Ñ N (m+1))
  have paid:LocalRatio Ñ:=(RunFormalChain.fromRun R).receipt
  exact raw_roll (loose A m) A.clock.kernel Ñ (freeForms A N (m+1)) (freeForms A N m)
    U (roam A N m) (A.blocks m 0).branches paid
    (inlet R simple (Nat.succ_le_of_lt hm)) (resin A N m hm) (horizon_ports A N m) i r

abbrev difference (N m i l:ℕ):raw (Hooks G) ℝ (l+1):=
  (fun n=>coil0 R.family.path.levels R.metals.O m N n i (l+1))-
    fun n=>originalAction R N m n i (l+1)

theorem purchase (simple:G.Simple){N m:ℕ}(hm:m<N)(i l:ℕ)(c:Side)(z:rule (Coarse G) c):
    Tendsto (fun p:Cover R m c=>(sheets R m c p:ℝ)⁻¹ •
      ((MvPolynomial.eval (Ker.convey (coverWin p.prop) z)
        (Blue.paint (l+1) (difference R N m i l (R.family.side m p.val))):ℝ):ℂ))
      (coverFilter R.family.S m c) (𝓝 0):=by
  classical
  let n (p:Cover R m c):=R.family.side m p.val
  let W (p:Cover R m c):=coverWin p.prop
  let Z (p:Cover R m c):=Ker.convey (W p) z
  let M (p:Cover R m c):=sheets R m c p
  let cap:ℝ:=∑v,‖z v‖
  have bounded (p:Cover R m c)(x:Site (n p) × Hooks G):‖Z p x‖≤cap:=
    Finset.single_le_sum (fun i _=>norm_nonneg (z i)) (Finset.mem_univ ((W p).cut x.1,x.2))
  have tracked:Yields (fun n=>originalAction R N m n i (l+1))
      (freshet R.family.path.levels R.metals.O N m i (l+1)):=(perch R.family.path.levels R.metals.O simple (RunFormalChain.fromRun R).receipt hm).growth i (l+1)
  have same:Yields (difference R N m i l) 0:=by
    simpa only [difference,sub_self] using (output R simple hm i (l+1)).sub tracked
  have raw:=WilsonVacuumPreResetTorusIntensive.original _ same n ((grows R m).comp tendsto_comap) Z bounded
  have scale (p:Cover R m c):(Fintype.card (Site c):ℝ)*(Fintype.card (Site (n p)):ℝ)⁻¹=(M p:ℝ)⁻¹:=by
    have count:Fintype.card (Site (n p))=M p*Fintype.card (Site c):=Shingle.received (W p).cut (W p).fold
    rw [count,Nat.cast_mul]
    field_simp
  simpa only [FVA1Physical.TwoReset.coverFilter,smul_smul,scale,smul_zero] using
    raw.const_smul (Fintype.card (Site c):ℝ)

end YM.Integration.WilsonVacuumPreResetFoldedCopyMoments
