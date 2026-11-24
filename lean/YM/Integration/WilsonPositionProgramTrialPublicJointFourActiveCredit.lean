import YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveKernel

/-! Polynomial active-row wages on the two original admitted cutoffs. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveCredit

open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Matrix PowerSeries Finset
open scoped BigOperators Classical
variable {G:Gauge}{F:Frame G 4}

open WilsonPositionProgramTrialPublicJointFourActiveKernel

structure Pass (A B:Coil F):Prop where
  ahead:A*B=1
  rewind:B*A=1
  live:Live B
  ground:∀i j:Alma F,sheet F i≠0 →lineS A 0 i j=(1:Wall F) i j

theorem crop {U:Type*}{x θ:U→ℝ}{A B:U→Wall F}(paid:CreditsS x θ A B):
    CreditsS x θ (fun n=>watch F (A n)) (fun n=>watch F (B n)):=by
  intro i j
  by_cases scalar:sheet F i=0
  · refine ⟨0,0,le_rfl,fun n=>?_⟩
    simp only [zero_mul,watched,if_pos scalar]
    exact twain.zero _
  · simpa only [watched,if_neg scalar] using paid i j

theorem start {A B:Coil F}(field:Pass A B):watch F (lineS A 0)=watch F 1:=by
  ext i j
  by_cases unit:sheet F i=0
  · simp [watched,unit]
  · simp [watched,unit,field.ground i j unit]

theorem run {U:Type*}{x θ:U→ℝ}(permit:Brite x θ)(e:ℕ)
    (A B C D:U → Coil F)(left:∀n,Pass (A n) (B n))(right:∀n,Pass (C n) (D n))
    (paid:∀q≤e,CreditsS x θ (fun n=>lineS (B n) q) (fun n=>lineS (D n) q)):
    ∀q≤e,CreditsS x θ (fun n=>watch F (lineS (A n) q)) (fun n=>watch F (lineS (C n) q)):=by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih=>
    intro loose
    by_cases zero:q=0
    · subst q
      simp_rw [fun n=>start (left n),fun n=>start (right n)]
      exact CreditsS.fixed permit _
    · have pos:0<q:=Nat.pos_of_ne_zero zero
      simp_rw [fun n=>step (left n).rewind q pos (left n).live (head (left n).ahead (left n).ground),
        fun n=>step (right n).rewind q pos (right n).live (head (right n).ahead (right n).ground)]
      apply CreditsS.neg
      apply CreditsS.sum _ permit
      intro j member
      have dates:=houseJ member
      exact (crop (paid j.1 (dates.1.trans loose))).prod
        (ih j.2 dates.2 (dates.2.le.trans loose)) permit

end YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveCredit
