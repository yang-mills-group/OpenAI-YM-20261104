import YM.Integration.WilsonIndependentMatchedPhysicalPeer
import YM.Integration.WilsonIndependentFittedMixedCash
/-! The exact reported finite-dose salary at the common physical kinetic clock. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedPhysicalPeerClock
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical
variable {G:Gauge}{h D k u e:ℕ}
local notation "CC" => Credit.leanC

open WilsonIndependentMatchedPhysicalPeer (reading amount)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonOlderFreshSoftCoverScalar (clock)

def chart (B:Cost):Cost→ₗ[ℝ]Cost:=
  (substAlgHom (R:=ℝ) (HasSubst.of_constantCoeff_zero' (by simp : constantCoeff (B*X)=0))).toLinearMap

def assay (A:Levels G)(O:ChartRatio G)(N m s q:ℕ)(g:ℝ):Cost→ₗ[ℝ]ℝ:=
  (reading q g).comp (chart (relativeF A O N s (m-s)))

theorem value (A:Levels G)(O:ChartRatio G)(N m s q:ℕ)(g:ℝ)(c:Cost)(before:s ≤ m):
    cash q g (embed (clock A O N m s c))=(assay A O N m s q g c:ℂ):=by
  have trueClock:=WilsonIndependentFittedRelativeClock.reported A O N s (m-s) c
  rw [Nat.add_sub_of_le before] at trueClock
  rw [trueClock]
  simp [cash,embed,assay,WilsonIndependentMatchedPhysicalPeer.reading,chart,reel,Finset.sum_apply]

def observed (A:Levels G)(O:ChartRatio G)(N m s q:ℕ)(g:ℝ){Q:SealR G}(x:Q.Rider):ℝ:=
  ∑i:Alma Q.F,‖cash q g (embed (clock A O N m s (x i)))‖

theorem paid (A:Levels G)(O:ChartRatio G)(N m s q:ℕ)(g:ℝ){Q:SealR G}(x:Q.Rider)(before:s ≤ m):
    observed A O N m s q g (Q:=Q) x=amount (Q:=Q) (assay A O N m s q g) x:=by
  simp [observed,amount,value A O N m s q g _ before]

theorem original (R:Run G)(simple:G.Simple)(v:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:h<D)(rails:Rails h k u e):
    let Q:=WilsonPositionProgramTrialNativeHome.reporter (G:=G) fit
    let L:=R.family.path.levels
    ∃B:Credit,∀ᶠ j:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N →
    ∀X:CutsP (hol G) Q.ans Q.path rails CC CC CC CC,X.ax=L → X.tx=R.metals.O → X.N=N → X.m=m →
    ∀s q g,s ≤ m → observed L R.metals.O N m s q g (Q:=Q) (dose X 1) ≤
      (Fintype.card (Alma Q.F):ℝ)*B.buy (zz L m)*observed L R.metals.O N m s q g (Q:=Q) (home Q X):=by
  intro Q L
  obtain ⟨B,bank⟩:=WilsonIndependentMatchedPhysicalPeer.original R simple v funded fit rails
  refine ⟨B,?_⟩
  filter_upwards [bank] with j grant
  intro m K N above gap endN X lev clocked prior base s q g before
  rw [paid _ _ _ _ _ _ _ _ before,paid _ _ _ _ _ _ _ _ before]
  exact grant m K N above gap endN X lev clocked prior base _

end YM.Integration.WilsonIndependentMatchedPhysicalPeerClock
