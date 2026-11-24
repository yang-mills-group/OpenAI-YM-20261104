import YM.Integration.WilsonSeparatedPrefixMovingHelperPlate
import YM.Integration.WilsonSeparatedPrefixMovingHelperQuote
import YM.Integration.WilsonOriginalPublicNodalHelperElection
import YM.Integration.WilsonIndependentNotebookMarkedEdge

/-! A grouped helper Court bearing its actual marked finite-return program, paid on the same optical master as the joined pupil. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingHelperElection
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Source Labels PertExtension RegulatorIR.Epoch RegulatorIR.Epoch.League
open XSpace Precision RegulatorIR RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Taping RegulatorIR.Uniform RegulatorIR.Calibration RegulatorIR.FVAAlt2 RegulatorIR.Momentum
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates Next.Foundations
open WilsonOriginalPublicNodalHelperShape (length physical)
open WilsonOriginalPublicNodalCommonRaw (Court)
open WilsonIndependentCutJoinPassport (All)
open WilsonIndependentSpoutPayrollRoute (reported)
open WilsonIndependentSpoutFundedClocks (clock)
open RegulatorIR.Clocks RegulatorIR.Ward RegulatorIR.Prim WilsonCoeffUV
open WilsonOriginalPublicNodalHelperElection (TwoNotebooks physicalCourt)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{H:Hol G}(R:PhysicalNext.Repeat.Legato.Run G)(P:Master H)(chart:ChartRatio G)(V:XSpace.Run)
    (e h k tier extra:ℕ)(p b u:ℕ)(γ:ℝ)(lo:0<γ)(hi:γ<1)
variable (Z:∀P:Patch,P.Branches R.family.path.levels.clock.kernel G)(col:G.ColorIndex)
    (B:WilsonIndependentEvenPassport.Menu P chart R.family.path.levels.clock.kernel V e h k tier extra)
    (late:5≤tier){X:Type}(m j:X → ℕ)(w:X → ℕ → ℕ)
    (blocks:∀x t,(R.family.S.block (m x+t)).val=V.ratio^(w x t))(r:X → ℕ)(ap:X → ℝ)(pos:∀x,0≤ap x)
local notation "N" => WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks
local notation "Gd" => WilsonOriginalPublicNodalHelperCircuit.circuit V (physical j w) r B.a tier B.positive (le_trans (by decide:4 ≤ 5) late)



local notation "BB" => R.family.path.levels.clock.kernel
local notation "YY" => Oracle.books (BB)
local notation "Film" => TwoNotebooks R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos

theorem original (simple:G.Simple)(before:Film)
    (grant:WilsonIndependentCutJoinPlate.Approved P chart (BB) V e h k tier extra B)
    (paid:WilsonIndependentPublicPlateGrant.floor (G:=G) (BB) tier (YY) p b u γ lo hi ≤ extra)
    (width:p ≤ u)(rate:0<b)(res:∀x,r x<B.a)(enough:∀x,0<length (physical j w) r B.a x):
    let dates:=length (physical j w) r B.a
    ∃(land:X→Levels G)(first:X→ℕ)(now:Film), now.F=before.F ∧
      (∀i H,physicalCourt R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos now i H =
        physicalCourt R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos before i H) ∧
      (∀x,WilsonIndependentPublicFreeTrain.Matches (land x) (Gd) (BB) (first x) x) ∧
      (∀f:Flap dates,∀per:ℕ,((land f.volW).clock.op (first f.volW+(dates f.volW-(f.offset+1))) per).patch=(Gd).pactP f) ∧
      (∀x t,t ≤ dates x→extendedY (B.price ⟨r x,res x⟩) (land x).S (first x+dates x) (first x+t)=B.price ⟨r x,res x⟩) ∧
      (∀x,All P (land x) chart (extendedY (B.price ⟨r x,res x⟩) (land x).S (first x+dates x)) e (first x) h k) ∧
      (∀v,RegulatorIR.Clocks.Matches p (((Gd).payroll (YY) G Z (sheet now.F')).bulk v) (reported land first v)) ∧
      (∀v,RegulatorIR.Ward.Squares p (tale (now.F' v).dine) (clock land (XSpace.Bare.chart G) first v) ∧
        RegulatorIR.Ward.Squares p (tale (sheet now.F' v).beta) (((clock land (XSpace.Bare.chart G) first v)⁻¹)^2)) ∧
      (∀(f:Flap dates)(n:Side),WilsonIndependentSpoutMeasuredHearing.Hearing (Gd) Z now.F' f (land f.volW) (first f.volW) p n) ∧
      ∀f:Flap dates,WilsonIndependentNotebookMarkedEdge.Reads (Gd) (YY) Z now.F' land first p f:=by
  intro dates
  obtain ⟨land,s,inc,flaps,tariffs,full⟩:=WilsonSeparatedPrefixMovingHelperPlate.original P chart (BB) V e h k tier extra B
    (by omega) (physical j w) r res enough grant
  obtain ⟨D,books,quiet,clocks,ears,rows⟩:=WilsonIndependentNotebookMarkedEdge.selected (Gd) (YY) Z land s simple inc p
  obtain ⟨flat,funds⟩:=WilsonSeparatedPrefixMovingHelperQuote.original P chart (BB) V e h k tier extra (YY) Z p b u γ lo hi
    B simple late width rate paid (physical j w) r res enough ap pos col D (books col)
  let now:Film:=⟨before.F,D,before.old,books col,before.flat,flat,before.phys,funds⟩
  exact ⟨land,s,now,rfl,fun _ _=>rfl,inc,flaps,tariffs,full,quiet,clocks,ears,rows⟩
end YM.Integration.WilsonSeparatedPrefixMovingHelperElection
end
