import YM.Integration.WilsonIndependentMatchedOwnHomeFiledAxes
import YM.Integration.WilsonSeparatedPrefixMovingFiledNumerical

/-! The same originally measured finite station bank pays every selected near
subroster and the one recurring exterior, before numerical evaluation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingFiledSeats
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialStationHome (chargeAt mass Seated)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n h D k u e:ℕ}{T:Type*}
local notation "C" => Credit.leanC
local notation "I" => Fin (n+1)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentFittedMixedCash (embed)
open WilsonIndependentFittedRosterCash (numerical reserve)
open WilsonMovingForkSharpSections (publicFrame)
open WilsonIndependentMatchedOwnHomeForkWindow (fits ranks)

open WilsonSeparatedPrefixMovingFiledContrast (roster offered axes)

theorem original (run:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(c:∀i,Verse (run.family.labels.level (l i)))
    (α:∀i,Alma (run.family.labels.level (l i))→ℝ)(Z B:I→Credit)(m K N:ℕ)
    (X:∀i,CutsP (hol G) ((deck (G:=G) l d admit) i).ans ((deck (G:=G) l d admit) i).path (own i) C C C C)
    (entered:WilsonPositionProgramTrialHomeFaces.Filed run W l d admit kind own c α Z B m K N X)
    (arity:Option T→ℕ)(far:I)(select:∀s,Fin (arity s+1)→I):
    let Q:=deck (G:=G) l d admit
    let b:Herit Q:=fun i=>home (Q i) (X i)
    let term:=fun s (i:Fin (arity s+1))=>Q (select s i)
    let live:=fun s=>offered (Q far) (term s) (b far) (fun i=>b (select s i))
    let paid:=fun i=>|chargeAt run.family.path.levels (Q i) e (B i) (Z i) m K| * charge e (c i) (α i)
    (∀i,(X i).pt=centralL run.family.path.levels run.metals.O N m K (Q i)
      (PermuteLens run.family.path.levels run.metals.O (Q i) N m (b i))+(X i).springP (X i).i) ∧
    (∀s (a:axes (Q far) (term s)),(∏i,live s i (a i))=
      b far (a 0)*∏i,b (select s i) (a i.succ)) ∧
    (∀s,reserve e (live s)≤paid far*∏i,paid (select s i)) ∧
    ∀s (g:ℝ),numerical e g (live s)=
      (∑a,‖cash e g (embed (b far a))‖)*∏i,∑a,‖cash e g (embed (b (select s i) a))‖:=by
  intro Q b term live paid
  refine ⟨fun i=>(entered i).2.1,fun s a=>?_,fun s=>?_,fun s g=>?_⟩
  · rw [Fin.prod_univ_succ];rfl
  · have h (i): (∑a,belt e (embed (b i a)))≤paid i:=by
      rw [WilsonIndependentMatchedOwnHomeFiledAxes.ticket_mass (Q i)];exact (entered i).2.2
    unfold reserve;rw [Fin.prod_univ_succ]
    change (∑a,belt e (embed (b far a)))*(∏i,∑a,belt e (embed (b (select s i) a)))≤_
    refine mul_le_mul (h far) (Finset.prod_le_prod ?_ (fun i _=>h (select s i))) ?_ ?_
    · exact fun i _=>Finset.sum_nonneg (fun a _=>WilsonPhysicalMarkedDefect.RawProduct.positive e _)
    · exact Finset.prod_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>WilsonPhysicalMarkedDefect.RawProduct.positive e _))
    · exact (Finset.sum_nonneg (fun _ _=>WilsonPhysicalMarkedDefect.RawProduct.positive e _)).trans (h far)
  · unfold numerical;rw [Fin.prod_univ_succ];rfl

end YM.Integration.WilsonSeparatedPrefixMovingFiledSeats
end
