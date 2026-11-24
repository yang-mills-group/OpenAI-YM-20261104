import YM.Integration.WilsonPositionProgramTrialHomeFaces
import YM.Integration.WilsonIndependentMatchedOwnHomeForkWindow

/-! The complete deposited finite source measured at the nominated original
home. Every coefficient is received on its own original incoming vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeFiledAxes
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
variable {G:Gauge}{n h D k u e:ℕ}{T:Type*}[Fintype T]
local notation "C" => Credit.leanC
local notation "I" => Fin (n+1)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentFittedMixedCash (embed)
open WilsonIndependentFittedRosterCash (numerical reserve)
open WilsonMovingForkSharpSections (publicFrame)
open WilsonIndependentMatchedOwnHomeForkWindow (fits ranks)

theorem ticket_mass (Q:SealR G)(p:ℕ)(b:Q.Rider):
    (∑a,belt p (embed (b a)))=WilsonPositionProgramTrialStationHome.mass Q p b:=by
  classical
  unfold WilsonPositionProgramTrialStationHome.mass
  apply Finset.sum_congr rfl
  intro i _
  unfold WilsonPhysicalMarkedDefect.RawProduct.belt
  have axis (j:ℕ):‖PowerSeries.coeff j (embed (b i))‖=‖PowerSeries.coeff j (b i)‖:=by
    rw [WilsonIndependentFittedMixedCash.embed,PowerSeries.coeff_map]
    exact Complex.norm_real _
  simp_rw [axis]
  exact (Fin.sum_univ_eq_sum_range (fun j=>‖PowerSeries.coeff j (b i)‖) (p+1)).symm

theorem original (run:Run G)(W:Initialize G)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(c:∀i,Verse (run.family.labels.level (l i)))
    (α:∀i,Alma (run.family.labels.level (l i))→ℝ)(Z B:I→Credit)(m K N:ℕ)
    (X:∀i,CutsP (hol G) ((deck (G:=G) l d admit) i).ans ((deck (G:=G) l d admit) i).path (own i) C C C C)
    (entered:WilsonPositionProgramTrialHomeFaces.Filed run W l d admit kind own c α Z B m K N X):
    let Q:=deck (G:=G) l d admit
    let b:Herit Q:=fun i=>home (Q i) (X i)
    (∀i,(X i).pt=centralL run.family.path.levels run.metals.O N m K (Q i)
      (PermuteLens run.family.path.levels run.metals.O (Q i) N m (b i))+(X i).springP (X i).i) ∧
    reserve e b ≤ ∏i,|chargeAt run.family.path.levels (Q i) e (B i) (Z i) m K| * charge e (c i) (α i):=by
  intro Q b
  refine ⟨fun i=>(entered i).2.1,?_⟩
  unfold reserve
  apply Finset.prod_le_prod
  · intro i _
    apply Finset.sum_nonneg
    intro j _
    unfold WilsonPhysicalMarkedDefect.RawProduct.belt
    positivity
  · intro i _
    rw [ticket_mass (Q i)]
    exact (entered i).2.2

def rows (run:Run G){D D':ℕ}(p:4<D)(pF:4<D')
    (b:Herit (deck (G:=G) (fun _:Fin 3=>4) (ranks D D') (fits p pF))):
    Herit (WilsonIndependentMatchedOwnHomeForestTariff.all (publicFrame run) p pF):=
  (WilsonIndependentMatchedOwnHomeForkWindow.same run p pF).symm ▸ b

theorem reserve_changed {A D:Fin (n+1)→SealR G}(same:A=D)(v:Herit D)(p:ℕ):
    reserve p (same.symm ▸ v:Herit A)=reserve p v:=by cases same;rfl

theorem numerical_changed {A D:Fin (n+1)→SealR G}(same:A=D)(v:Herit D)(p:ℕ)(g:ℝ):
    numerical p g (same.symm ▸ v:Herit A)=numerical p g v:=by cases same;rfl

end YM.Integration.WilsonIndependentMatchedOwnHomeFiledAxes
end
