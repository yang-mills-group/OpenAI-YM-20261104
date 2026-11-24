import YM.Integration.OriginalMarkedPhysicalCash
import YM.Integration.WilsonLongContactWeighted
import YM.Extra.ITERATION_NO_LOSS.Continuity

/-! Restrict the orders and spatial prices of the actual representation, simultaneously
retaining every numerical activity, hard guard and signed marked density. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactRebudget
open Lattice Wilson RG Source Labels Push Precision Pressure Pressure.Stores Pressure.Tube
open ConnectedActivityE6 Extra.Iteration Extra.Iteration.Comparison
open Set MeasureTheory
open scoped Classical BigOperators
variable {G : Gauge} {n c : Side} {S : StepData c n} {Q : Rep G n}

/-- The sole altered record is the derivative budget. -/
def atBudget (Q : Rep G n) (B : BudgetPoint) : Rep G n := {Q with p := B}

theorem exponent {B : BudgetPoint} (h : HasBudget Q.p B) (U : Config G n) :
    Q.exponent U = (atBudget Q B).exponent U := by
  simp only [Rep.exponent,atBudget,PathData.inChannels,PathData.principal,PathData.baseTerm,
    PathData.atomSeries,Atom.placed,Activities.additive,Activities.regularOccurrence,h.threshold]

theorem law {B : BudgetPoint} (h : HasBudget Q.p B) (U : Config G n) :
    (atBudget Q B).eval U = Q.eval U := by
  change Real.exp ((atBudget Q B).exponent U)*Q.activities.gas B U = _
  rw [←exponent h]
  change Real.exp (Q.exponent U)*Q.activities.gas B U = Real.exp (Q.exponent U)*Q.activities.gas Q.p U
  congr 1
  simp only [Activities.gas,Activities.gasOccurrence,Activities.admissible,h.threshold]
  apply tsum_congr
  intro k
  split_ifs <;> rfl

theorem intake {P : Teller G} {T : Tube G S} {x : ℝ} {B : BudgetPoint}
    (old : Intake P T x Q) (h : HasBudget Q.p B) (exactSupport : P.top.supportExponent=B.supportExponent) :
    Intake P T x (atBudget Q B) := by
  exact ⟨old.ready,⟨old.received.path,old.received.clip,h.threshold.symm.trans old.received.temp⟩,
    ⟨old.cap.paths,h.valid old.cap.labels le_rfl le_rfl⟩,exactSupport,old.height,
    h.B.symm.trans old.sizes,old.window⟩

variable {k : ℕ} {F : Frame G k} {L : Hol G} (P : Coefficient F n) (o : Site n)

theorem source {B : BudgetPoint} (h : HasBudget Q.p B) (C : SectionData F) (U : Config G n) :
    P.density o C (atBudget Q B) U = P.density o C Q U := by
  unfold Coefficient.density
  rw [law h,←exponent h]
  have he : P.exponentialEntry o C (atBudget Q B) U = P.exponentialEntry o C Q U := by
    simp only [Coefficient.exponentialEntry,Coefficient.maskedTerm,atBudget,h.threshold]
  rw [he]
  congr 2
  apply tsum_congr
  intro k
  simp only [Coefficient.marked,atBudget,Activities.admissible,h.threshold]

theorem format {B : BudgetPoint} (h : HasBudget Q.p B) (issued : P.Format o L Q) :
    P.Format o L (atBudget Q B) := by
  refine ⟨fun i => ?_,issued.origin,issued.identity_null,issued.projects,?_,issued.carried,
    issued.invariant,?_,issued.borel⟩
  · refine { (issued.smooth i) with
      smooth := fun U hu => ((issued.smooth i).smooth U (h.threshold.symm ▸ hu)).of_le (by exact_mod_cast h.order)
      hasDerivs := fun U hu A l hl => (issued.smooth i).hasDerivs U (h.threshold.symm ▸ hu) A l (hl.trans_le h.order) }
  · intro i U nonzero
    change (Q.activities.forced i).eligible B.threshold U
    rw [←h.threshold]
    exact issued.forcing i U nonzero
  · intro i
    change UsesFinal B.threshold (Q.activities.forced i).support (P.forced i)
    rw [←h.threshold]
    exact issued.supported i

theorem remBound {B : BudgetPoint} (h : HasBudget Q.p B) {κ w : ℝ} (paid : P.remBound o Q κ w) :
    P.remBound o (atBudget Q B) κ w := by
  obtain ⟨a,b,ha,hb,hw,hκ,⟨e,sold,he⟩,f,bill,hf⟩ := paid
  refine ⟨a,b,ha,hb,hw,hκ,⟨e,?_,fun i => h.toHasJets.sup (he i)⟩,f,?_,hf⟩
  · change SumBudget (fun i=>B.mass (P.support i) (e i)) a
    exact Cost.mono sold (fun i=>mul_nonneg (Real.exp_pos _).le (he i).1) (fun i=>h.mass _ (he i).1)
  · change SumBudget (fun i=>B.mass (Q.activities.forced i).support (f i)) (κ*b)
    exact Cost.mono bill (fun i=>mul_nonneg (Real.exp_pos _).le (hf i).1) (fun i=>h.mass _ (hf i).1)

end YM.Integration.WilsonLongContactRebudget
