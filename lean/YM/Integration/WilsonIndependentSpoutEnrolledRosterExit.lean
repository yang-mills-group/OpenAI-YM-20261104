import YM.Integration.WilsonIndependentSpoutRawRosterExit
import YM.Integration.WilsonIndependentSpoutOriginalMarkedJourney
import YM.Integration.WilsonIndependentMatchedOpeningComplete

/-! The true regulated Wilson orbit pays for the scalar of its entire normalized Mer history on a matching submitted word. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutEnrolledRosterExit
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open WilsonIndependentMatchedOpeningRoster (field)
open scoped Classical
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(K:KernelChoices)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(V:XSpace.Run)(a j:ℕ)(ha:0<a)(late:4≤j)
    (A:Requests a → Levels G)(s:Requests a → ℕ)(D:Tent (M V a))(p:ℕ)

theorem original (simple:G.Simple)(O:ChartRatio G)(ratio:LocalRatio O)(γ:ℝ)(ap:Requests a → ℝ)
    (priced:WilsonIndependentPublicRosterBook.Priced R W K Y Z V a j ha late p γ ap D)
    (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads (S V a ha j late) Y Z D A s p f)
    (I:Type)(σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index){E:I→ℕ}(cut:∀i,d i<E i)
    (arms:Composite I)(sample:Requests a → Sample 2)(sites:Requests a → I → Cover)(x:Requests a → Room)
    (c₀:ℝ)(board:∀w,(sample w).F=V.step w.val)
    (reach:∀w,WilsonIndependentRawRosterBudget.span (x w) (sites w) arms≤ap w) (small:0<c₀)
    (safe:((S V a ha j late).dialect Y G Z (sheet D)).cushion c₀ x)(q:ℕ)(hq:q≤p):
    ∃ k₀:ℕ,∃ H₀:ℝ,0≤H₀ ∧ ∀w,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
          (film R W σ d key (sample w) (sites w) arms))-
        (note (WilsonIndependentSpoutOriginalMarkedJourney.source A s O (Page.finallyW (M V a) w)
          (cruises (A w) O (s w+M V a w) (arms.accounts (degree R d key))
            (s w+M V a w) (s w) (field R W σ d key cut (sites w) arms)) q 0):ℂ)‖≤
        H₀*(1+ap w+Real.log ((V.step w.val).p.side.val:ℝ))^k₀*((V.step w.val).p.side.val:ℝ)^(-(γ/2)):=by
  simp_rw [WilsonIndependentSpoutOriginalMarkedJourney.entry A s O ratio,
    WilsonIndependentSpoutHaarHistory.original ratio (Bare.chart_ratio G)]
  exact WilsonIndependentSpoutRawRosterExit.original R W K Y Z V a j ha late A s D p simple γ ap priced read
    I σ d key arms sample sites x c₀ board reach small safe _ (fun w=>
      (WilsonIndependentMatchedOpeningComplete.original R W σ d key cut arms (sites w) (L:=M V a) A s w).1)
    (fun w=>WilsonIndependentMatchedOpeningComplete.measured R W σ d key cut arms (sites w)
      (L:=M V a) A s w p) q hq

end YM.Integration.WilsonIndependentSpoutEnrolledRosterExit
