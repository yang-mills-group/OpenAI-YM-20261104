import YM.Integration.WilsonPositionProgramTrialPaidPanel
import YM.Integration.WilsonPositionProgramTrialBufferedHome

/-! A common vacuum buffer for the actual cutoff-dependent measured roster and its stopped word. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialHomeRoster
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open Extra.Histories Motion PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialPaidPanel (Layout Dated bill Home)
open WilsonPositionProgramTrialStationHome (Seated chargeAt mass)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n h D k u e:ℕ}(R:Run G)(W:Initialize G)
local notation "C" => Credit.leanC
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "I" => Fin (n+1)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:h<D)(rails:Rails h k u e)(l d:I→ℕ)(admit:∀i,l i<d i)(kind:I→Bool)
    (own:∀i,Rails (l i) k u e)(cap:capP (deck (G:=G) l d admit)≤k):
    let Q:=deck (G:=G) l d admit
    ∃α:∀i,Alma (R.family.labels.level (l i))→ℝ,(∀i s,0≤α i s) ∧
    ∃Z B:I→Credit,∀ᶠ floor:ℕ in atTop,
    ∀m K host,floor ≤ host → host ≤ m → m ≤ K →
    ∀(data:I→Layout R K)(tests:I→ℝ)(width ε:ℝ),
    1≤zz L m → Compar (L).S (zz L) host m ≤ width → 0<ε →
    ∃upper:ℕ,∃clears:K ≤ upper,∀N N' per (old:upper ≤ N),upper ≤ N' →
    ∀files:∀i,Dated R (l i) K N per (data i) (clears.trans old),
    ∃X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) C C C C,
      let b:Herit Q:=fun i=>home (Q i) (X i)
      (∀i,
        let t:=data i
        let c:=WilsonPositionProgramTrialPaidHome.source R (files i).arm t.radius t.phase t.test
        Seated R (Q i) (own i) m K N (Shrine (plate (sectionAt R W (kind i) (l i)) (admit i)) c)
          (charge e c (α i)) (X i) ∧
        (X i).pt=centralL L O N m K (Q i) (PermuteLens L O (Q i) N m (b i))+(X i).springP (X i).i ∧
        mass (Q i) e (b i) ≤ |chargeAt L (Q i) e (B i) (Z i) m K| *bill R (l i) e K t (α i)) ∧
      ∀(F:Wilt Q)(y:ℝ)(o:CellR),Bough Q F y width tests →
        let prior:=stopped L O Q F b m K N host y o
        let fresh:=stopped L O Q F b m K N' host y o
        (∀r t,r≤e → Fruit 0 1 u (prior.2 r t-fresh.2 r t) ε) ∧
        ∀r,r≤e → ∀t:Fin 0→YForest G,‖prior.2 r 0 t-fresh.2 r 0 t‖≤ε:=by
  intro Q
  have paid i:=WilsonPositionProgramTrialPaidPanel.original R W simple v funded (admit i) (own i)
    (kind i) (admit i) (own i).hk
  choose α nn Z B registered using paid
  refine ⟨α,nn,Z,B,?_⟩
  have common:∀ᶠ j:ℕ in atTop,∀i,Home R W (Q i) (own i) (l i) (kind i) (admit i)
      (α i) (Z i) (B i) j:=Filter.eventually_all.2 registered
  filter_upwards [common,WilsonPositionProgramTrialBufferedHome.original R simple v funded fit rails
    l d admit cap] with floor homes stability
  intro m K host awake past placed data tests width ε warm bound small
  let income i:=|chargeAt L (Q i) e (B i) (Z i) m K| *bill R (l i) e K (data i) (α i)
  obtain ⟨upper,clears,limit⟩:=stability m K host awake past placed tests income width ε warm bound small
  refine ⟨upper,clears,?_⟩
  intro N N' per old new files
  have enroll i:=homes i m K N per (awake.trans past) placed (clears.trans old) (data i) (files i)
  choose X seats fields capital using enroll
  refine ⟨X,fun i=>⟨seats i,fields i,capital i⟩,?_⟩
  intro F y o fundedTest
  exact limit N N' (fun i=>home (Q i) (X i)) F y o old new fundedTest capital

end YM.Integration.WilsonPositionProgramTrialHomeRoster
end
