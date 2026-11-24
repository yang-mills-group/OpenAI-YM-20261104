import YM.Integration.WilsonLongContactSectorSeat
import YM.Integration.WilsonLongContactProtectedRun

/-! The actual selected single address at the capped quotation, on both
the original old signed density and the restricted consecutive field budgets. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactProtectedAddress
open Function Filter Set Lattice Wilson Pressure RG Tree Precision Marker Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Lotus
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm Supply Input Org Testing
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Extra.Iteration.Comparison WilsonLongContactRebudget WilsonLongContactSectorCash
open LocalLTE MergeProof Progress.DirectedRecipe Baffle
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {Q : Rep G n} {B : BudgetPoint}

variable {V : Type} [DecidableEq V] {J : Request V} {Δ : Daisy.Charity.RG12.Decal G}
    {extra : Stage → ℕ → ℝ} {γ : ℝ} {R : Run G}
    {ρ : WilsonLongContactSectorProtection.Premium G J.outputFieldOrder}
    {paid : WilsonLongContactSectorProtection.Paid J Δ extra γ ρ R.kit} {A : NumericSchedule R.family J}
    {Γ : Census V} {z : LocalFormal.Datum R.family Γ}
local notation "Y₁" => R.family.path.rep z.cutoff z.period (z.level+1)
local notation "p₁" => A.inputNorm z.level
local notation "S₀" => R.alloy.B.a.clock.op z.level z.period

theorem original (e : WilsonLongContactProtectedRun.Field J Δ extra γ R ρ paid A z) (simple : G.Simple)
    (o : Site (R.family.S.side (z.level+1) z.period)) (s : Γ.Mode) (hs : s.val.Nonempty)
    (X : RegularAddress (R.family.S.side (z.level+1) z.period)) (copy : ℕ)
    (f : Config G (R.family.S.side (z.level+1) z.period) → ℂ) {w : ℝ}
    (regular : (Y₁).p.Regular X.support f) (price : (Y₁).p.supBounds o X.support f w) (part : Bool) :
    let i := blankRow _ (X,copy)
    ∃ N : Menu.Hat Γ (atBudget (Y₁) (p₁)), N.s=s ∧ N.M.turn=.logKey i ∧ N.M.crest=X.support ∧ N.M.weight=w ∧
      (∀ U,N.M.cicada U=Port.scaleQ part (masked (Y₁).p.threshold X.support f U)*(Y₁).eval U) ∧
      (∀ U,Menu.amount N U=Poly.send s ((Port.scaleQ part (masked (Y₁).p.threshold X.support f U):ℂ)*Port.ink part)) ∧
      ∀ (F : Forest (S₀).ratio) (χ : Chi) (W : Config G (R.family.S.side z.level z.period)) (tag : (S₀).Choices),
        Healthy (A.outputNorm z.level).threshold (Brim.plate e.cash.choose i).support W →
        Scrim (Brim.foyer e.cash.choose i F χ W tag) (Brim.mapcase e.cash.choose i F) := by
  intro i
  obtain ⟨M,mode,key,crest,weight,hf,amount,_⟩ := WilsonLongContactAddress.filed R simple
    z.cutoff z.period (z.level+1) z.below o Γ s hs X copy f w regular price part
  let N : Menu.Hat Γ (atBudget (Y₁) (p₁)) := {M with M:=WilsonLongContactSectorSeat.leaf e.budget M.M}
  have index : N.M.turn=.logKey i := key
  refine ⟨N,mode,index,(WilsonLongContactSectorSeat.reach M.M.turn).trans crest,weight,?_,amount,?_⟩
  · intro U
    rw [WilsonLongContactAddress.density N.M i index U,law e.budget]
    exact congrArg (fun v : ℝ => v*(Y₁).eval U) (congrFun hf U)
  · intro F χ W tag healthy
    exact Brim.grove e.cash.choose i tag F healthy e.plays.rehearsed.temp_eq


end YM.Integration.WilsonLongContactProtectedAddress
