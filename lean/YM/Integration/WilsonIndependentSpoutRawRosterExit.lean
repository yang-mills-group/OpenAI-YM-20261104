import YM.Integration.WilsonIndependentSpoutFundedReportBook

/-! The true regulated Wilson orbit pays for the scalar of its entire normalized Mer history on a matching submitted word. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutRawRosterExit
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open WilsonIndependentNotebookPayrollMark (source)
open scoped Classical
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(K:KernelChoices)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(V:XSpace.Run)(a j:ℕ)(ha:0<a)(late:4≤j)
    (A:Requests a → Levels G)(s:Requests a → ℕ)(D:Tent (M V a))(p:ℕ)

theorem original (simple:G.Simple)(γ:ℝ)(ap:Requests a → ℝ)
    (priced:WilsonIndependentPublicRosterBook.Priced R W K Y Z V a j ha late p γ ap D)
    (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads (S V a ha j late) Y Z D A s p f)
    (I:Type)(σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    (sample:Requests a → Sample 2)(sites:Requests a → I → Cover)(x:Requests a → Room)
    (c₀:ℝ)(board:∀w,(sample w).F=V.step w.val)
    (reach:∀w,WilsonIndependentRawRosterBudget.span (x w) (sites w) arms≤ap w) (small:0<c₀)
    (safe:((S V a ha j late).dialect Y G Z (sheet D)).cushion c₀ x)
    (X:Requests a → Era G ℝ)(auth:∀w,Auth (arms.accounts (degree R d key)) (X w))
    (entry:∀w,RegulatorIR.Clocks.Matches p (bank R W σ d key arms (sites w))
      (source A s (Page.opening (M V a) w) (X w)))(q:ℕ)(hq:q≤p):
    ∃ k₀:ℕ,∃ H₀:ℝ,0≤H₀ ∧ ∀w,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
          (film R W σ d key (sample w) (sites w) arms))-
        (note (source A s (Page.finallyW (M V a) w)
          (cruises (A w) (Bare.chart G) (s w+M V a w) (arms.accounts (degree R d key))
            (s w+M V a w) (s w) (X w)) q 0):ℂ)‖≤
        H₀*(1+ap w+Real.log ((V.step w.val).p.side.val:ℝ))^k₀*((V.step w.val).p.side.val:ℝ)^(-(γ/2)):=by
  let C:=S V a ha j late
  let T:=C.payroll Y G Z (sheet D)
  let n:=arms.accounts (degree R d key)
  let B:=WilsonIndependentRawRosterOrbit.report R W σ d key arms T sites
  obtain ⟨l,H,positive,reading⟩:=priced I σ d key arms sample sites x c₀ board reach small safe q hq
  refine ⟨l,H,positive,fun w=>?_⟩
  have opening:RegulatorIR.Clocks.Matches p (B.main (Page.opening (M V a) w)) (source A s (Page.opening (M V a) w) (X w)):=entry w
  have arrived:=WilsonIndependentSpoutMarkJourney.original C Y Z D A s p read simple n B w 0 (Nat.zero_le _)
    (X w) (auth w) opening (M V a w) (Nat.zero_le _) le_rfl
  have result:RegulatorIR.Clocks.Matches p (B.main (Page.finallyW (M V a) w))
      (source A s (Page.finallyW (M V a) w) (cruises (A w) (Bare.chart G) (s w+M V a w) n (s w+M V a w) (s w) (X w))):=by
    simpa only [Page.finallyW,Nat.sub_self,Nat.sub_zero,Nat.add_zero] using arrived
  exact (congrArg (fun t=> ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
    (film R W σ d key (sample w) (sites w) arms))-(note (t 0):ℂ)‖) (result q hq)) ▸ reading w

end YM.Integration.WilsonIndependentSpoutRawRosterExit
