import YM.Integration.WilsonMovingMentorSchools

/-! The real opportunity salaries of the original Mentor course after its purchased delay.
The held register, allowable postage and scout, purchased block, fine widths and order are the
ones chosen by the same Wilson factor. -/
noncomputable section
namespace YM.Integration.WilsonMovingMentorSalary
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
variable {G : Gauge}

open WilsonMovingShadowPrices (Ask support)
open Brim.WilsonMovingSingleton (Year spring)
open FullVolume WilsonLimitConstruction

open QuadraticLocal.Mentor

/-- The original salary for each possible count and rank of an admitted Opportunity, available
at every physical temperature above the actual delay. -/
def Earned {G : Gauge} : Prediction G := fun {_} {D} {A} F =>
  ∀ j i, StepStages j i → ∀ k s : ℕ, k ≤ i → 1 ≤ s → s ≤ i →
    ∃ certs : Salary G (D.L j), ∀ t : ℝ, A.delay.betaEntry j ≤ t →
      SummerS (F.target j i) k s (F.walls j i) (F.shape.μ j i) (D.L j)
        (F.shape.o j i) (F.scout j i) certs t

def Admitted {G : Gauge} (a : Ask) : Prediction G := fun {_} {_} {_} F =>
  WilsonMovingMentorSchools.Admitted a F ∧ Earned F

theorem bought {G : Gauge} (simple : G.Simple) (ask : Ask) (slow : ℝ → ℝ) :
    WilsonMovingCommonPrices.AllPrices ask slow (@WilsonMovingStoredFactor.OnMenu G (@Admitted G ask)) := by
  intro sheet cost targets E charts C v baton wanting wage
  have brackets := WilsonMovingMentorTuition.before ask E wanting wage
  obtain ⟨lower,salary⟩ := QuadraticLocal.Mentor.leases targets (fun j i _ => (brackets j i).1)
    (fun j i _ => (brackets j i).2.1)
  obtain ⟨u,buy⟩ := WilsonMovingMentorSchools.bought simple ask slow sheet cost targets E charts C v baton wanting wage
  refine ⟨u ⊔ lower,?_⟩
  intro l hl upper D w U Z φ S θ record fee V pocket caps
  obtain ⟨old,late⟩ := sup_le_iff.mp hl
  obtain ⟨Y,floor,full⟩ := buy l old upper D w U Z φ S θ record fee V pocket caps
  have tables (j i : ℕ) (st : StepStages j i) (k s : ℕ) (hs : 1 ≤ s) :=
    salary j i st (D.L j) ((late j).trans (D.large j).need)
      (w j i) (Z.μ j i) (Z.consumes j i st).1 (Z.consumes j i st).2.1
      (Z.o j i) (φ j i) (S j i) (pocket.price j i st) k s hs
  let due (j i : ℕ) (t : ℝ) := ∀ (st : StepStages j i) (k s : Fin (i+1)) (hs : 1 ≤ s.val),
    SummerS (targets j i) k.val s.val (w j i) (Z.μ j i) (D.L j) (Z.o j i) (S j i) (tables j i st k s hs).choose t
  have eventual (j i : ℕ) (st : StepStages j i) : ∀ᶠ t in atTop, due j i t := by
    have each (k s : Fin (i+1)) : ∀ᶠ t in atTop, ∀ hs : 1 ≤ s.val,
        SummerS (targets j i) k.val s.val (w j i) (Z.μ j i) (D.L j) (Z.o j i) (S j i) (tables j i st k s hs).choose t := by
      by_cases pos : 1 ≤ s.val
      · exact (tables j i st k s pos).choose_spec.mono fun _ h _ => h
      · exact Eventually.of_forall fun _ h => False.elim (pos h)
    have all := eventually_all.mpr fun k => eventually_all.mpr fun s => each k s
    exact all.mono fun _ h _ k s hs => h k s hs
  obtain ⟨up,-,raised,receipts⟩ := collect_upper Y.betaEntry _ (fun j =>
      eventually_transitions j atTop _ (fun i st => eventual j i st))
  let Y' : Delays θ := {Y with betaEntry:=up}
  have move : DelayLe Y Y' := ⟨raised,le_rfl,le_rfl,le_rfl⟩
  refine ⟨Y',floor.trans move,?_⟩
  intro A next K I marked B light alloy η q E' X J K' b hZ hc hm hq
  refine ⟨full A (move.trans next) K I marked B light η q E' X J K' b hZ hc hm hq,?_⟩
  intro j i st k s high start fit
  let k' : Fin (i+1) := ⟨k,by omega⟩
  let s' : Fin (i+1) := ⟨s,by omega⟩
  refine ⟨(tables j i st k s start).choose,?_⟩
  intro t ht
  exact receipts j t ((next.beta j).trans ht) i st st k' s' start

end YM.Integration.WilsonMovingMentorSalary
end
